{-# OPTIONS --safe --without-K #-}

module Syllogism where

  module _
    (Train Puff Thomas Aristotele : Set)
    where

    thomas-puffs : (Train → Puff) → (Thomas → Train) → (Thomas → Puff)
    thomas-puffs train-puffs thomas-is-train thomas = train-puffs (thomas-is-train thomas)

  module _
    (Middle Subject Predicate : Set)
    where

    barbara : (Middle → Predicate) → (Subject → Middle) → (Subject → Predicate)
    barbara major minor subject = major (minor subject)
