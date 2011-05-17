#!r6rs

;; authors: noah goodman

;;this library generates the church-specific header definitions.
;;the header includes:
;;  church-make-xrp
;;  church-apply, church-eval
;;  mcmc code, including the query primitives assumed by the de-sugarring transform.
;;  deterministic (non-higher-order) scheme primitives wrapped up into church- forms. (NOTE: should have a mechanism to provide additional primitives -- add external defs arg to generate-header.)

;;this should generate scheme compatible with r4rs+srfi1 (some additional defines are needed for stalin, etc, that don't have srfis).

;;NOTE: assumes a bunch of random sampling/scoring primitives, which should be provided from GSL (eg. in our external/math-env.ss).


(library
 (church header)

 (export generate-header)

 (import (rnrs)
         (_srfi :1) ; lists
         (church readable-scheme)
         )

 (define *storethreading* false)

;;;main procedure to make the header.
;;;any free "church-" variable in the program that isn't provided explicitly is assumed to be a scheme primitive, and a church- definition is generated for it.
 (define (generate-header storethreading free-variables external-defs)
   (set! *storethreading* storethreading)
   (let* ((special-defs (generate-special))
          (def-symbols (map (lambda (d) (if (pair? (second d)) (first (second d)) (second d)))
                            (append special-defs inverses external-defs))) ;;get defined symbols
          (leftover-symbols (filter (lambda (v) (not (memq v def-symbols))) (filter church-symbol? (delete-duplicates free-variables))))
          (primitive-defs (map (lambda (s) (primitive-def s)) leftover-symbols)))
     (append external-defs primitive-defs special-defs inverses)))
 
;;;things to wrap up primitive functions and symbols for use within transformed code:
 (define (prefix-church symb) (string->symbol (string-append "church-" (symbol->string symb))))
 (define (church-symbol? symb) (and (< 7 (length (string->list (symbol->string symb))))
                                    (equal? "church-" (list->string (take (string->list (symbol->string symb)) 7)))))
 (define (un-prefix-church symb) (if (church-symbol? symb)
                                     (string->symbol (list->string (drop (string->list (symbol->string symb)) 7)))
                                     symb))

 ;;an inverse symbol should be bound to a scheme proc in header that takes cs and args list and returns values of args...
(define (get-inverse-symbol s)
  (case s
    ((procand) 'procand-inverse)
    ((cons) 'cons-inverse)
    ((car) 'first-inverse)
    ((second) 'second-inverse)
    ((cdr) 'rest-inverse)
    ((list) 'list-inverse)
    ;((list-ref) 'id-list-ref-inverse)
    ((procor) 'procor-inverse)
    ((equal?) 'equal?-inverse)
    ((eqv?) 'equal?-inverse)
    [else #f]))

(define (wrap-primitive symb . nargs)
  (let* ((actual-args (if (null? nargs) 'args (repeat (first nargs) gensym)))
         (arguments  `(cs address store . ,actual-args))
         (application (let* ([inverse-symbol (get-inverse-symbol symb)])
                        (if inverse-symbol
                            `(apply ,symb (,inverse-symbol cs address store ,(if (null? nargs) 'args `(list ,@actual-args))))
                            (if (null? nargs)
                                `(apply ,symb (map (lambda (a) (church-force-deep church-*wildcard* address store a )) args))
                                ;`(begin (display ',symb)(newline) (apply ,symb (map (lambda (a) (church-force-deep church-*wildcard* address store a )) args)))
                                `(,symb ,@(map (lambda (a) `(church-force-deep church-*wildcard* address store ,a)) actual-args)))))
                      ))
    ;(if *storethreading*
     ;   `(lambda ,arguments (list ,application store))
        `(lambda ,arguments ,application)))
 
 (define (primitive-def symb)
   `(define ,symb ,(wrap-primitive (un-prefix-church symb))))


;;;special header functions including xrp handling code and the counterfactual update used in MH.
 (define (generate-special)
   `(
;;;
     ;;take a church proc, cache return value on address (used for short-circuiting memoized proc evaluation)
     (define not-set 'no-cached-value-set) ;fixme: make (gensym))
     (define (cache proc)
       (define cache-hash not-set)
       (lambda (cs address store . args)
         (if (null? (first address))
             ;;has no args, don't need a hash table
             (begin (when (eq? not-set cache-hash) (set! cache-hash (church-apply cs address store proc args)))
                    cache-hash)
             ;;has args, need a hash-table
             (begin (when (eq? not-set cache-hash) (set! cache-hash (make-hash-table)))
                    (hash-table-ref cache-hash address (lambda () (let ((val (church-apply cs address store proc args)))
                                                                    (hash-table-set! cache-hash address val)
                                                                    val)))))))
     
     ;;misc church primitives
     (define (church-apply cs address store proc args)
       (apply (church-force church-*wildcard* address store proc) cs address store (church-force church-*wildcard* address store args)))

     ;;requires compile, eval, and environment to be available from underlying scheme....
     (define (church-eval cs addr store sexpr) ;;FIXME: constraints?
       ((eval `(letrec ,(map (lambda (def)
                              (if (symbol? (cadr def))
                                  (list (cadr def) (caddr def))
                                  `(,(car (cadr def)) (lambda ,(cdr (cadr def)) ,@(cddr def)))))
                            (compile (list sexpr) '()))
                church-main)
             (environment '(rnrs)
                          '(rnrs mutable-pairs)
                          '(_srfi :1)
                          '(rename (church external math-env) (sample-discrete discrete-sampler))
                          '(rename (only (ikarus) gensym pretty-print exact->inexact) (gensym scheme-gensym))
                          '(_srfi :19)
                          '(church compiler)
                          '(rnrs eval)  ))
             addr store))
     
     (define (church-get-current-environment cs address store) (error 'gce "gce not implemented"))
     (define church-true #t)
     (define church-false #f)
     (define church-*wildcard* 'wildcard);(gensym 'wilcard))
     ;(define church-pair ,(wrap-primitive 'cons 2))
     (define church-pair ,(wrap-primitive 'cons 2))
     (define church-first ,(wrap-primitive 'car 1))
     (define church-rest ,(wrap-primitive 'cdr 1))
     (define (procor . args) (if (null? args) #f (if (car args) #t (apply procor (cdr args)))))
     (define church-or ,(wrap-primitive 'procor))
     (define (procand . args) (if (null? args) #t (if (eq? #f (car args)) #f (apply procand (cdr args)))))
     (define church-and ,(wrap-primitive 'procand))
     (define church-scheme-equal? ,(wrap-primitive 'equal? 2))

     (define (wildcard? v) (if (pair? v)
                               (if (eq? (car v) church-*wildcard*) #t (wildcard? (cdr v)))
                               (eq? v church-*wildcard*)))

     (define (intersect a b) 
       (cond ((wildcard? a) b)
             ((wildcard? b) a)
             (else (lset-intersection eq? a b))))

     (define (singleton? cs) (and (not (wildcard? cs)) (pair? cs) (null? (cdr cs))))
           
     
     (define (lev-dist) (error "lev-dist not implemented"))

     ;;for laziness and constraints:
     (define (church-force cs address store val)
       (if (and (pair? val) (eq? (car val) 'delayed))
           (church-force cs address store ((cadr val) cs address store 'd))
           val))
     (define (church-force-deep cs address store val)
       (let ((fv (church-force cs address store val)))
         ;(display fv)(newline)
         (if (pair? fv)
             (cons (church-force-deep (if (wildcard? cs) cs (map car cs)) address store (car fv))
                   (church-force-deep (if (wildcard? cs) cs (map cdr cs)) address store (cdr fv)))
             fv)))
    

;;;
     ;;stuff for xrps (and dealing with stores):
     (define (make-store xrp-draws xrp-stats score tick enumeration-flag) (list xrp-draws xrp-stats score tick enumeration-flag))
     (define (make-empty-store) (make-store (make-addbox) (make-addbox) 0.0 0 #f))
     (define store->xrp-draws first)
     (define store->xrp-stats second)
     (define store->score third)
     (define store->tick fourth)
     (define store->enumeration-flag fifth) ;;FIXME: this is a hacky way to deal with enumeration...

     (define (church-reset-store-xrp-draws cs address store)
       (return-with-store store
                          (make-store (make-addbox)
                                      (store->xrp-stats store)
                                      (store->score store)
                                      (store->tick store)
                                      (store->enumeration-flag store))
                          'foo))

     (define (return-with-store store new-store value) ,(if *storethreading*
                                                            '(list value new-store)
                                                            '(begin (set-car! store (car new-store))
                                                                    (set-cdr! store (cdr new-store))
                                                                    value)))

     (define alist-insert
       (lambda (addbox address info)
         (cons (cons address info) addbox)))

     ;; returns pair of info and remaining addbox. returns false if no
     ;; info with this address.
     (define alist-pop
       (lambda (addbox address)
         (if (null? addbox)
             (cons #f '())
             (if (equal? address (caar addbox))
                 (cons (cdar addbox) (cdr addbox))
                 (let ((ret (alist-pop (cdr addbox) address)))
                   (cons (car ret) (cons (car addbox) (cdr ret))))))))

     (define (make-empty-alist) '())
     (define alist-size length)
     (define alist-empty? null?)
     
     ;; addboxes hold info indexed by the evaluation address.
     ;; doesn't attempt to maintain order.

     ;; alist addbox
     (define add-into-addbox alist-insert)
     (define pull-outof-addbox alist-pop)
     (define make-addbox make-empty-alist)
     (define addbox->alist (lambda (addbox) addbox))
     (define alist->addbox (lambda (alist) alist))
     (define addbox-size alist-size)
     (define addbox-empty? alist-empty?)

     ;; trie addbox
     ;; (define make-addbox make-empty-trie)
     ;; (define add-into-addbox trie-insert)
     ;; (define pull-outof-addbox trie-pop)
     ;; (define addbox->alist trie->alist)
     ;; (define alist->addbox alist->trie)
     ;; (define addbox-size trie-size)
     ;; (define addbox-empty? trie-empty?)

     (define (make-xrp-draw address value xrp-name proposer-thunk ticks score support)
       (list address value xrp-name proposer-thunk ticks score support))
     (define xrp-draw-address first)
     (define xrp-draw-value second)
     (define xrp-draw-name third)
     (define xrp-draw-proposer fourth)
     (define xrp-draw-ticks fifth) ;;ticks is a pair of timer tick when this xrp-draw is touched and previous touch if any.
     (define xrp-draw-score sixth)
     (define xrp-draw-support seventh)
     (define (xrp-draw-fwd x) (list-ref x 8))
     (define (xrp-draw-rev x) (list-ref x 9))

     ;;note: this assumes that the fns (sample, incr-stats, decr-stats, etc) are church procedures.
     ;;FIXME: what should happen with the store when the sampler is a church random fn? should not accumulate stats/score since these are 'marginalized'.
     (define (church-make-xrp cs address store xrp-name sample incr-stats decr-stats score init-stats hyperparams proposer support)
       (let* ((xrp-name (church-force church-*wildcard* address store xrp-name))
              (sample (church-force church-*wildcard* address store sample))
              (incr-stats (church-force church-*wildcard* address store incr-stats))
              (decr-stats (church-force church-*wildcard* address store decr-stats))
              (score (church-force church-*wildcard* address store score))
              (init-stats (church-force church-*wildcard* address store init-stats))
              (hyperparams (church-force church-*wildcard* address store hyperparams))
              (proposer (church-force church-*wildcard* address store proposer))
              (support (church-force church-*wildcard* address store support)))
       (return-with-store
        store
        (let* ((ret (pull-outof-addbox (store->xrp-stats store) address))
               (oldstats (car ret))
               (reststatsbox (cdr ret))
               (tick (store->tick store)))
          (if (and (not (eq? #f oldstats)) (= tick (second oldstats))) ;;reset stats only if this is first touch on this tick.
              store
              (make-store (store->xrp-draws store)
                          (add-into-addbox reststatsbox address (list init-stats tick))
                          (store->score store)
                          tick
                          (store->enumeration-flag store))))
        (let* ((xrp-address address)
               (proposer (if (null? proposer)
                             (lambda (cs address store operands old-value) ;;--> proposed-value forward-log-prob backward-log-prob
                               (let* ((dec (decr-stats church-*wildcard* address store old-value (caar (pull-outof-addbox (store->xrp-stats store) xrp-address)) hyperparams operands))
                                      (decstats (second dec))
                                      (decscore (third dec))
                                      (inc (sample church-*wildcard* address store decstats hyperparams operands))
                                      (proposal-value (first inc))
                                      (incscore (third inc)))
                                 (list proposal-value incscore decscore)))
                             proposer)))
          (lambda (cs address store . args)
            ;(display "constraint set is ")(display cs)(display "  at address ")(display address)(display "\n")
            ;(display "xrp draw store ")(display (store->xrp-draws store))(newline)
            (let* ((args (map (lambda (a) (church-force church-*wildcard* address store a)) args)) ;;FIXME: args doesn't need to be forced here, except for proposer...
                   (tmp (pull-outof-addbox (store->xrp-draws store) address)) ;;FIXME!! check if xrp-address has changed?
                   (old-xrp-draw (car tmp))
                   (rest-xrp-draws (cdr tmp))
                   (old-tick (if (eq? #f old-xrp-draw) '() (first (xrp-draw-ticks old-xrp-draw))))
                   )
              ;;if this xrp-draw has been touched on this tick, as in mem, don't change score or stats.
              (if (equal? (store->tick store) old-tick)
                  (return-with-store store store (xrp-draw-value old-xrp-draw))
                  (let* ((tmp (pull-outof-addbox (store->xrp-stats store) xrp-address))
                         (stats (caar tmp))
                         (rest-statsbox (cdr tmp))
                         (support-vals (if (null? support) church-*wildcard* (support church-*wildcard* address store stats hyperparams args)))
                         (support-vals (intersect cs support-vals))
                         ;;this commented out code is for incemental updates...
                         ;; (tmp (if (eq? #f old-xrp-draw)
                         ;;          (sample address store stats hyperparams args) ;;FIXME: returned store?
                         ;;          (let* ((decret (decr-stats address store (xrp-draw-value old-xrp-draw) stats hyperparams args)) ;;FIXME!!! old args and xrp stats?
                         ;;                 (incret (incr-stats address store (xrp-draw-value old-xrp-draw) (second decret) hyperparams args)))
                         ;;            (list (first incret) (second incret) (- (third incret) (third decret))))))
                         (tmp (if (eq? #f old-xrp-draw)
                                  ;;initialize the xrp-draw:
                                  (if (store->enumeration-flag store) ;;hack to init new draws to first element of support...
                                      (incr-stats church-*wildcard* address store (first support-vals) stats hyperparams args)
                                      (if (singleton? cs);(and (not (wildcard? cs)) (pair? cs) (null? (cdr cs)))
                                          (incr-stats church-*wildcard* address store (first cs) stats hyperparams args) ;;singleton cs is deterministic on init...
                                          (sample church-*wildcard* address store stats hyperparams args))) ;;FIXME: returned store?
                                  ;;re-use existing xrp-draw value:
                                  (incr-stats church-*wildcard* address store (xrp-draw-value old-xrp-draw) stats hyperparams args)))
                         (value (first tmp))
                         (new-stats (list (second tmp) (store->tick store)))
                         (incr-score (third tmp)) ;;FIXME: need to catch measure zero xrp situation?
                         ;(xrp-draw-address address)
                         (new-xrp-draw (make-xrp-draw address
                                                      value
                                                      xrp-name
                                                      (lambda (cs address store state)
                                                        ,(if *storethreading*
                                                             '(list (first
                                                                     (church-apply church-*wildcard*
                                                                                   (mcmc-state->address state)
                                                                                   (mcmc-state->store state)
                                                                                   proposer
                                                                                   (list args value)))
                                                                    store)
                                                             '(let ((store (cons (first (mcmc-state->store state)) (cdr (mcmc-state->store state)))))
                                                                ;(display "proposing at address ")(display xrp-draw-address)
                                                                ;(display "  support is ")(display support-vals)(newline)
                                                                (church-apply church-*wildcard* (mcmc-state->address state) store proposer (list args value)))))
                                                      (cons (store->tick store) old-tick)
                                                      incr-score
                                                      support-vals))
                         (new-store (make-store (add-into-addbox rest-xrp-draws address new-xrp-draw)
                                                (add-into-addbox rest-statsbox xrp-address new-stats)
                                                (+ (store->score store) incr-score)
                                                (store->tick store)
                                                (store->enumeration-flag store))))
                    (return-with-store store new-store value))))))))  )

       ;;mcmc-state structures consist of a store (which captures xrp state, etc), a score (which includes constraint enforcement), and a return value from applying a nfqp.
       ;;constructor/accessor fns: mcmc-state->xrp-draws, mcmc-state->score, mcmc-state->query-value, church-make-initial-mcmc-state.
       (define (make-mcmc-state store value address) (list store value address))

       (define mcmc-state->store first)
       (define mcmc-state->address third)
       ;(define (mcmc-state->xrp-draws state) (store->xrp-draws (mcmc-state->store state)))
       (define (church-mcmc-state->xrp-draws cs address store state) (store->xrp-draws (mcmc-state->store state)))
       
       (define (church-mcmc-state->score cs address store state) ;;FIXME: since this is primitive, it deep forces state, which includes the (delayed) query pair.
         (let ((cond-val (church-force church-*wildcard* (mcmc-state->address state) (mcmc-state->store state) (first (second state)))))
           (if (not (eq? #t cond-val))
               -inf.0 ;;enforce conditioner.
               (store->score (mcmc-state->store state)))))

       ;;this assumes that nfqp returns a thunk, which is the delayed query value. we force (apply) the thunk here, using a copy of the store from the current state.
       (define (church-mcmc-state->query-value cs address store state) ;;FIXME: since this is primitive, it deep forces state, which includes the (delayed) query pair.
         ;,(if *storethreading*
              ;'(first (church-apply church-*wildcard* (mcmc-state->address state) (mcmc-state->store state) (cdr (second state)) '()))
              (let* ((mcmcstore (cons (first (mcmc-state->store state)) (cdr (mcmc-state->store state))))
                     (val (church-force-deep church-*wildcard* (mcmc-state->address state) mcmcstore (cdr (second state))))) ;;FIXME: do we need the deep force?
                val))
                 ;(church-force church-*wildcard* (mcmc-state->address state) store
                 ;              (church-apply church-*wildcard* (mcmc-state->address state) store (cdr (second state)) '()))))

       ;;this captures the current store/address and packages up an initial mcmc-state.
       (define (church-make-initial-mcmc-state cs address store)
                                        ;(for-each display (list "capturing store, xrp-draws has length :" (length (store->xrp-draws store))
                                        ;                        " xrp-stats: " (length (store->xrp-stats store)) "\n"))
         ;,(if *storethreading*
          ;    '(list (make-mcmc-state store 'init-val address) store)
         (make-mcmc-state (cons (first store) (cdr store)) 'init-val address))

       ;;this is like church-make-initial-mcmc-state, but flags the created state to init new xrp-draws at left-most element of support.
       ;;clears the xrp-draws since it is meant to happen when we begin enumeration (so none of the xrp-draws in store can be relevant).
       (define (church-make-initial-enumeration-state cs address store)
         ;;FIXME: storethreading.
         (make-mcmc-state (make-store '() (store->xrp-stats store) (store->score store) (store->tick store) #t)
                          'init-val address))

       ;;this is the key function for doing mcmc -- update the execution of a procedure, with optional changes to xrp-draw values.
       ;;  takes: an mcmc state, a normal-from-proc, and an optional list of interventions (which is is a list of xrp-draw new-value pairs to assert).
       ;;  returns: a new mcmc state and the bw/fw score of any creations and deletions.
       ;;must exit with store being the original store, which allows it to act as a 'counterfactual'. this is taken care of by wrapping as primitive (ie. non church- name).
       (define (church-counterfactual-update cs address store state nfqp . interventions)
         ;(display "cfu, xrps: ")(display (church-mcmc-state->xrp-draws cs address store state))(newline)
         (let* ((new-tick (+ 1 (store->tick (mcmc-state->store state))))
                (interv-store (make-store (fold (lambda (interv xrps)
                                                  (add-into-addbox (cdr (pull-outof-addbox xrps (xrp-draw-address (first interv))))
                                                                   (xrp-draw-address (first interv))
                                                                   (make-xrp-draw (xrp-draw-address (first interv))
                                                                                  (cdr interv)
                                                                                  (xrp-draw-name (first interv))
                                                                                  (xrp-draw-proposer (first interv))
                                                                                  (xrp-draw-ticks (first interv))
                                                                                  'dummy-score ;;dummy score which will be replace on update.
                                                                                  (xrp-draw-support (first interv))
                                                                                  )))
                                                (store->xrp-draws (mcmc-state->store state))
                                                interventions)
                                          (store->xrp-stats (mcmc-state->store state)) ;;NOTE: incremental differs here (adjust score for new values).
                                          0.0 ;;NOTE: incremental differs here ;;(store->score (mcmc-state->store state))
                                          new-tick ;;increment the generation counter.
                                          (store->enumeration-flag (mcmc-state->store state))
                                          ))
                ;;application of the nfqp happens with interv-store, which is a fresh pair, so won't mutate original state.
                ;;after application the store must be captured and put into the mcmc-state.
                ;(ret ,(if *storethreading*
                ;          '(church-apply church-*wildcard* (mcmc-state->address state) interv-store nfqp '()) ;;return is already list of value + store.
                ; '(list (church-apply church-*wildcard* (mcmc-state->address state) interv-store nfqp '()) interv-store)) 
                (value (church-apply church-*wildcard* (mcmc-state->address state) interv-store nfqp '()))
                (new-store interv-store) ;;capture store, which may have been mutated.
                (ret2 (if (store->enumeration-flag new-store)
                          (list new-store 0)
                          (clean-store new-store))) ;;FIXME!! need to clean out unused xrp-stats?
                (new-store (first ret2))
                (cd-bw/fw (second ret2))
                (proposal-state (make-mcmc-state new-store value (mcmc-state->address state))))
           ;(display "cfu post xrps: ")(display (church-mcmc-state->xrp-draws cs address store proposal-state))(newline)
           (list proposal-state cd-bw/fw)))

       ;;we need to pull out the subset of new-state xrp-draws that were touched on this pass,
       ;;at the same time we want to accumulate the bw score of these deleted xrp-draws and the fw score of any new ones.
       ;;FIXME: this doesn't play nice with addbox abstraction, and is linear time in the number of xrp-draws.
       ;;FIXME: this method won't work with caching since used xrp-draws may not get 'touched'...
       ;;FIXME: assumes new choices drawn from the conditional prior -- that's currently true but not general.
       (define (clean-store store)
         (let* ((state-tick (store->tick store))
                (draws-bw/fw
                 (let loop ((draws (addbox->alist (store->xrp-draws store)))
                            (used-draws '())
                            (bw/fw 0.0))
                   (if (null? draws)
                       (list used-draws bw/fw)
                       (if (= (first (xrp-draw-ticks (cdar draws))) state-tick)
                           (if (null? (cdr (xrp-draw-ticks (cdar draws))))
                               ;;this was a new xrp-draw, accumulate fw prob:
                               (loop (cdr draws) (cons (car draws) used-draws) (- bw/fw
                                                                                  (if (singleton? (xrp-draw-support (cdar draws)))
                                                                                      0.0
                                                                                      (xrp-draw-score (cdar draws))) ;;NOTE: incremental differs here
                                                                                  ))
                               ;;this xrp-draw existed already:
                               (loop (cdr draws) (cons (car draws) used-draws) bw/fw))
                           ;;this xrp-draw was not used in last update, drop it and accumulate bw prob:
                           (loop (cdr draws) used-draws (+ bw/fw
                                                           (if (singleton? (xrp-draw-support (cdar draws)))
                                                                                      0.0
                                                                                      (xrp-draw-score (cdar draws))) ;;NOTE: incremental differs here
                                                           )))))))
           (list (make-store (alist->addbox (first draws-bw/fw))
                             (store->xrp-stats store)
                             (store->score store)
                             (store->tick store)
                             (store->enumeration-flag store))
                 (second draws-bw/fw))))


       ;;this function takes a church proc and a proposer to use for it, returns a wrapped proc that stores the call and details: address, xrp-draws, return value
       ;(define (church-with-proposer address store fn proposer)
       ;  'foo
       ;  )


       ;; MCMC with counterfactuals

       (define *intervention* (make-parameter #f))

       (define (church-*intervention* cs address store)
         (*intervention*))
         
       (define (church-with-interventions cs address store state proc)
         (parameterize ([*intervention* #t])
                       (church-force-deep church-*wildcard*
                                          (mcmc-state->address state)
                                          (mcmc-state->store state)
                                          (proc church-*wildcard*
                                                (mcmc-state->address state)
                                                (mcmc-state->store state)))))

       )
   )

(define inverses
  '(
         ;;inverses (take a list of delayed args, return a lists of arg values)
     (define (procand-inverse cs address store args)
        (cond
         ((equal? cs '(#t)) ;;handle singleton true cs.
          (map (lambda (a) (church-force '(#t) address store a)) args))
         (else
          (church-force-deep church-*wildcard* address store args))))

     (define (procor-inverse cs address store args)
        (cond
         ((equal? cs '(#t)) ;;handle singleton true cs.
          (let loop ((argsleft args))
            (if (null? (cdr argsleft))
                (cons (church-force '(#t) address store (car argsleft)) '())
                (let ((nextargval (church-force church-*wildcard* address store (car argsleft))))
                  (if nextargval (cons nextargval '()) (cons nextargval (loop (cdr argsleft))))))))
         ((equal? cs '(#f)) ;;handle singleton false cs.
          (map (lambda (a) (church-force '(#f) address store a)) args))
         (else
          (church-force-deep church-*wildcard* address store args))))

     ;;note: cons does not force it's unconstrained args, to permit lazy pairs.
     (define (cons-inverse cs address store args)
       (if (and (singleton? cs) (pair? (car cs)))
           ;;handle singleton constraints that is a pair
           (let ((csl (caar cs));(church-force church-*wildcard* address store (caar cs)))
                 (csr (cdar cs)));(church-force church-*wildcard* address store (cdar cs))))
             (list
              (if (wildcard? (list csl)) ;;only force if not widcard
                  (car args)
                  (church-force (list csl) address store (car args)))
              (if (wildcard? (list csr)) ;;only force if not widcard
                  (cadr args)
                  (church-force (list csr) address store (cadr args)))))
           ;;otherwise just return (possibly delayed) args -- don't force...
           args))

     (define (list-inverse cs address store args)
       (if (and (singleton? cs) (list? (car cs)))
           ;;handle singleton constraints that is a list
           (map (lambda (x a)
                  (if (wildcard? (list x)) a (church-force (list x) address store a)))
                (car cs)
                args)
           ;;otherwise just return (possibly delayed) args -- don't force...
           args))

     (define (id-list-ref-inverse cs address store args) ;;this sequences the index first, hence can't find the index that will match a cs..
       (let ((lst (first args))
             (index (church-force church-*wildcard* address store (second args))))
         (list (append (take lst index)
                       (list (church-force cs address store (list-ref lst index)))
                       (drop lst (+ 1 index)))
               index)))
     
     (define (di-list-ref-inverse cs address store args) ;;this sequences the domain first, hence can't force the domain to contain a match to the cs..
       (if (wildcard? cs)
           args
           (let* ((lst (church-force church-*wildcard* address store (first args))) ;;FIXME: force-list
                  (index (second args))
                  (cs-indices (map (lambda (c) (list-index lst c)) cs))) ;;FIXME: find duplicate entries in domain.
             (list lst
                   (church-force cs-indices address store index)))))

      (define (first-inverse cs address store args)
        (let ((pr (church-force church-*wildcard* address store (car args))))
          (list (cons (church-force cs address store (car pr))
                      (cdr pr)))))

      
      (define (second-inverse cs address store args)
        (let ((pr (church-force church-*wildcard* address store (car args))))
          (list (cons (car pr)
                      (cons (church-force cs address store (cadr pr))
                            (cddr pr))))))

      (define (rest-inverse cs address store args)
        (let ((pr (church-force church-*wildcard* address store (car args))))
          (list (cons (car pr)
                      (church-force cs address store (cdr pr))))))

     (define (equal?-inverse cs address store args)
       (if (equal? cs '(#t))
           (let* ((a (church-force-deep church-*wildcard* address store (car args)))
                  (b (church-force-deep (list a) address store (cadr args))))
             (list a b))
           (map (lambda (a) (church-force church-*wildcard* address store a)) args)))
     ))

)
