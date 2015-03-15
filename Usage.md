Summary of compiler usage.

# Introduction #

The compiler (church-compiler) isn't meant to be called by itself, instead there are several scripts that call the compiler, add wrappers for particular scheme compilers, then call the scheme compiler.

For example, compile-church-ikarus does this for ikarus. You use it with something like:
> ./compile-church-ikarus church/tmp.church

# External Scheme Definitions #

You can provide (deterministic, non-higher-order) scheme functions to be used in your church program. Use this with the -e flag. For example:
> ./compile-church-ikarus myprog.church -e myhelpers.sc