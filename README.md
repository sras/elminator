# Elminator [![Build Status](https://travis-ci.com/sras/elminator.svg?branch=master)](https://travis-ci.com/sras/elminator)

Generate Elm type definitions and JSON encoders/decoders from Haskell source (for Elm 0.19 and 0.18)

1. Supports generation of polymorphic types (as well as concrete ones) in Elm from possibly polymorphic Haskell types, including types with phantom type variables.
2. Supports generation of recursively defined types.
3. Generates code that does not depend on external Elm libraries.
4. Does not have limits on the number of fields that the constructors of your type can have.
5. Supports JSON encoding options exported by the Aeson library comprehensively. The tests in [TravisCI](https://travis-ci.com/sras/elminator) exhaustively check the Elm/Haskell round tripping of values for all possible configurations of Aeson.options
6. Supports generation of code that depend on user defined types and encoders/decoders in Elm.

Hackage page: [https://hackage.haskell.org/package/elminator](https://hackage.haskell.org/package/elminator)

### How to use?

To generate Elm code for a Haskell type, the Haskell type needs to have an instance of the `ToHType` type class.
This can be automatically derived, provided all your constructor field types have `ToHType` instances. A sample can be seen below. Please note that language extensions `DeriveGeneric` and `DeriveAnyClass` should be enabled to make this work.

```haskell
{-# Language DeriveGeneric #-}
{-# Language DeriveAnyClass #-}

module Lib  where

import Elminator
import GHC.Generics (Generic)

data SingleCon = SingleCon Int String deriving (Generic, ToHType)

```

Since this library uses template Haskell to look up type information (in addition to Generics), we need to run the code generation code in a template Haskell splice.
A usage sample can be seen in the following code used in the round trip tests for this library.


```haskell
{-# Language OverloadedStrings #-}
{-# Language TemplateHaskell #-}

module CodeGen where

import Data.Proxy
import Elminator
import Data.Text.IO
import Data.Text

import Lib

elmSource :: Text
elmSource =
  $(generateFor Elm0p19 myDefaultOptions "Autogen" (Just "./elm-app/src/Autogen.elm") $ do
      include (Proxy :: Proxy SingleCon) $ Everything Mono
      include (Proxy :: Proxy SingleRecCon) $ Everything Mono
      include (Proxy :: Proxy SingleConOneField) $ Everything Mono
      include (Proxy :: Proxy SingleRecConOneField) $ Everything Mono
      include (Proxy :: Proxy TwoCons) $ Everything Mono
      include (Proxy :: Proxy TwoRecCons) $ Everything Mono
      include (Proxy :: Proxy BigCon) $ Everything Mono
      include (Proxy :: Proxy BigRecCon) $ Everything Mono
      include (Proxy :: Proxy MixedCons) $ Everything Mono
      include (Proxy :: Proxy Comment) $ Everything Mono
      include (Proxy :: Proxy WithMaybes) $ Everything Mono
      include (Proxy :: Proxy WithSimpleMaybes) $ Everything Mono
      include (Proxy :: Proxy (WithMaybesPoly (Maybe String) Float)) $
        Definiton Poly
      include
        (Proxy :: Proxy (WithMaybesPoly (Maybe String) Float))
        EncoderDecoder
      include (Proxy :: Proxy (Phantom ())) $ Everything Poly
      include (Proxy :: Proxy (TypeWithPhantom Float)) $ Everything Poly
      include (Proxy :: Proxy RecWithList) $ Everything Mono
      include (Proxy :: Proxy IndRecStart) $ Everything Mono
      include (Proxy :: Proxy IndRec2) $ Everything Mono
      include (Proxy :: Proxy IndRec3) $ Everything Mono
      include (Proxy :: Proxy NTSingleCon) $ Everything Mono
      include (Proxy :: Proxy NTSingleCon2) $ Everything Poly
      include (Proxy :: Proxy Tuples) $ Everything Mono
      include (Proxy :: Proxy NestedTuples) $ Everything Mono
      include (Proxy :: Proxy (NestedTuplesPoly ())) $ Definiton Poly
      include (Proxy :: Proxy (TypeWithExt ())) $ Everything Poly
      include (Proxy :: Proxy (WithEmptyTuple ())) $ Everything Poly
      include (Proxy :: Proxy (Phantom2 ())) $ Everything Poly
      include (Proxy :: Proxy PhantomWrapper) $ Everything Poly)

-- The `generateFor` function accepts an elm version (Elm0p19 or Elm0p18), a value of type `Options` from the Aeson library
-- , a module name for the generated module, and an optional `FilePath` to which the generated source will be written to, and a `Builder` value.
-- The `Builder` is just a `State` monad that aggregates the configuration parameters from the include
-- calls. The first parameter of the include function is a `proxy` value that denotes the type that requires Elm code generation.
-- The second value is a value of type `GenOption` that selects which entities needs to be generation, and also selects if the
-- type generated at Elm should be polymorphic. It is defined as follows.

data GenOption
  = Definiton PolyConfig  -- Generate Type definition in Elm. PolyConfig field decides if the type has to be polymorphic
  | EncoderDecoder -- Generate Encoder and Decoder in Elm
  | Everything PolyConfig -- Generate both type definition, encoders and decoders. PolyConfig field decides if the type has to be polymorphic.

data PolyConfig
  = Mono | Poly
```

A sample of generated Elm code can be seen [here](https://bitbucket.org/sras/elminator-test/src/master/elm-app/src/Autogen.elm)

### How to explicitly map a Haskell type to an Elm type

Say you have this type defined in Haskell

```
  data Product = Product { pName :: String, pWeight :: Decimal }
```

We can derive `ToHType` for the above type just fine. This is because we have this general ToHType instance that use the `Typeable` instances to create primitive type representation.

```
instance {-# OVERLAPPABLE #-} (Typeable a) => ToHType a where
  toHType p = pure $ mkHType p
```

Even though we are able to derive HType instance, the generated code end up looking something like the following

```
type Product = Product { pName : String, pWeight : DecimalRaw }

encodeProduct : Product  -> E.Value
encodeProduct a =
 case a of
  Product x -> E.object ([ ("pName", E.string (x.pName))
                         , ("pWeight", encodeDecimalRaw (x.pWeight))])

decodeProduct : D.Decoder Product
decodeProduct  =
 D.oneOf ([ let
             mkProduct a1 a2 =
              Product ({pName = a1, pWeight = a2})
            in D.map2 (mkProduct) (D.field ("pName") (D.string)) (D.field ("pWeight") (encodeDecimalRaw))])
```

But there is no `DecimalRaw` type on the Elm side. So in this case, we might want to use `Float` on Elm side whenever we have a `Decimal` field in Haskell.

This can be done as follows

```
  instance ToHType Decimal where
    toHType _ = toHType (Proxy :: Proxy Float)
```

This gives us usable Elm code.

```
type Product = Product { pName : String, pWeight : DecimalRaw }

encodeProduct : Product -> E.Value
encodeProduct a =
 case a of
  Product x -> E.object ([ ("pName", E.string (x.pName))
                         , ("pWeight", encodeDecimalRaw (x.pWeight))])

decodeProduct : D.Decoder Product
decodeProduct  =
 D.oneOf ([ let
             mkProduct a1 a2 =
              Product ({pName = a1, pWeight = a2})
            in D.map2 (mkProduct) (D.field ("pName") (D.string)) (D.field ("pWeight") (decodeDecimalRaw))])
```

Note that this only works if both types have compatible JSON representations. The Aeson instances
should take care of this on the Haskell side.

### Tests

This is being tested by round tripping a bunch of JSON encoded values from an Elm front end to a Haskell back end, where it is decoded and sent back to Elm where it is again decoded and checked for equality with the value that was initially sent. These right now, are in the form of a Python script that walks through the full range of Aeson options, make the Haskell build and auto generated Elm source for each, and then test the round tripping of included types using a headless Chromium browser. The tests at [TravisCI](https://travis-ci.com/sras/elminator) use this process as well. The test repo is separate for now and is available at https://bitbucket.org/sras/elminator-test.

### Installing

If you are using the Stack tool, then for the time being, you have to add Elminator to the 'extra-deps' section of stack.yaml as follows (Please use the latest available version here).

```yaml
extra-deps:
  elminator-0.2.1.0
```

