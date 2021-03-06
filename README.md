prelude-safeenum
================
[![Hackage version](https://img.shields.io/hackage/v/prelude-safeenum.svg?style=flat)](https://hackage.haskell.org/package/prelude-safeenum) 
[![Hackage-Deps](https://img.shields.io/hackage-deps/v/prelude-safeenum.svg?style=flat)](http://packdeps.haskellers.com/specific?package=prelude-safeenum)
[![TravisCI Build Status](https://img.shields.io/travis/wrengr/prelude-safeenum.svg?style=flat)](https://travis-ci.org/wrengr/prelude-safeenum) 
[![CircleCI Build Status](https://circleci.com/gh/wrengr/prelude-safeenum.svg?style=shield&circle-token=b57517657c556be6fd8fca92b843f9e4cffaf8d1)](https://circleci.com/gh/wrengr/prelude-safeenum)

A redefinition of the Prelude's `Enum` class in order to render it
safe. That is, the Haskell Language Report defines `pred`, `succ`,
`fromEnum`, and `toEnum` to be partial functions when the type is
`Bounded`. This is unacceptable. We define a new type-class hierarchy
for enumeration which is safe and also generalizes to cover types
which can only be enumerated in one direction.
    

## Install

This is a very simple package and should be easy to install. You
should be able to use any of the following standard methods to
install it.

    -- With cabal-install and without the source:
    $> cabal install prelude-safeenum
    
    -- With cabal-install and with the source already:
    $> cd prelude-safeenum
    $> cabal install
    
    -- Without cabal-install, but with the source already:
    $> cd prelude-safeenum
    $> runhaskell Setup.hs configure --user
    $> runhaskell Setup.hs build
    $> runhaskell Setup.hs test
    $> runhaskell Setup.hs haddock --hyperlink-source
    $> runhaskell Setup.hs copy
    $> runhaskell Setup.hs register

The test step is optional and currently does nothing. The Haddock
step is also optional.


## Portability

An attempt has been made to keep this library portable; however,
it does rely on a few language extensions. All the required language
extensions are:

* CPP
* GeneralizedNewtypeDeriving
* MagicHash - only for GHC
* Trustworthy - only for GHC >= 7.1

The GeneralizedNewtypeDeriving extension is used for brevity in
Data.Number.CalkinWilf. If you'd like to use this package with a
compiler that does not support that extension, contact the maintainer
and it can be removed.

This package is only "Trustworthy" rather than "Safe" for two
reasons: (1) Data.Number.CalkinWilf uses GeneralizedNewtypeDeriving,
and (2) Prelude.SafeEnum imports GHC.Exts for build/foldr fusion
and for the Char instances.


## Links

* [Website](http://cl.indiana.edu/~wren/)
* [Blog](http://winterkoninkje.dreamwidth.org/)
* [Twitter](https://twitter.com/wrengr)
* [Hackage](http://hackage.haskell.org/package/prelude-safeenum)
* [Darcs](http://code.haskell.org/~wren/prelude-safeenum)
* [GitHub (clone)](https://github.com/wrengr/prelude-safeenum)
* [Haddock (Darcs version)
    ](http://code.haskell.org/~wren/prelude-safeenum/dist/doc/html/prelude-safeenum)
