## Borrowed session types in Idris2

* requires `idris2` version 0.7.0 with library `linear` (version
  `2024060800` required) installed in the path
* to compile, change directory to `src` and run the sh script `compile.sh`
* there is no specific output, the point is that the encoding compiles successfully

## Files

(all in subdirectory `src`)

* `Linear.idr` patched version of the like-named file from the Idris2 library `linear`. Patches by the maintainer.
* `LinearUnion.idr` patched version of the library file `Data.OpenUnion.idr` adapted by us to accept linear types.
* `Sessionx.idr` patched version of the session library https://test.idris-lang.org/Idris2/linear/source/System.Concurrency.Session.html to accommodate transmitting linear types.
* `Splittablex.idr` our implementation of splittable channels as documented in the paper. The functions are named as in the paper and the remaining definitions are commented.

## Expected behavior

When using docker, stay in the root directory and execute the
following commands.

```sh
> docker build -t bst-idris . # takes a while ...
> docker run -it bst-idris sh
# sh compile.sh
1/4: Building Linear (Linear.idr)
2/4: Building LinearUnion (LinearUnion.idr)
3/4: Building Sessionx (Sessionx.idr)
4/4: Building Splittablex (Splittablex.idr)
# 
```

Voila! The encoding of borrowed session types compiled successfully.
