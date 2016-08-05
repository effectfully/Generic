module Generic.Lib.Data.String where

open import Data.String.Base renaming (toList to toListˢ; _++_ to _++ˢ_) public

open import Generic.Lib.Decidable
import Data.String as String

instance
  StringEq : Eq String
  StringEq = viaBase String._≟_
