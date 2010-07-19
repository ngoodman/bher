(import (rnrs)
        (rnrs mutable-pairs) ;;because the header uses set-car! when note storethreading.
        (_srfi :1) ;;provides some list functions that are used.
        (rename (church external math-env) (sample-discrete discrete-sampler)) ;;this provides the gsl sampling/scoring functions.
	(rename (only (ikarus) gensym ;;this is needed.
	      	       exact->inexact) ;;this isn't really needed.
		(gensym scheme-gensym))
	)

