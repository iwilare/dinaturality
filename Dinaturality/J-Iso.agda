{-# OPTIONS --safe --without-K #-}

{-
  We show that the maps defined in `Dinaturalit/J.agda` and `Dinaturalit/J-Inverse.agda` are isomorphisms.

  The two isomorphism conditions are themselves split in
  two different files to avoid going out of memory.
-}
module Dinaturality.J-Iso where

import Dinaturality.J-IsoA
import Dinaturality.J-IsoB
