module Request where


open import Categories.Functor
open import Categories.Category.Instance.Sets
open import Level
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality 

open ≡-Reasoning
open import Pipes


send
  :  {m : Functor (Sets 0ℓ) (Sets 0ℓ)}
  -> {a' a b' b : Set}
  -> {x x' : Set}
  -> a
  -> Proxy (Functor.F₀ m) x' x a' a a'
send a = respond a pure

{-
                              /===> b
                             /      |
     +---------+            /  +----|----+            +---------+
     |         |           /   |    v    |            |         |
 x' <==       <== b' <==\ / x'<==       <== c'    x' <==       <== c'
     |    f    |         X     |    g    |     =      | f //> g |
 x  ==>       ==> b  ===/ \ x ==>       ==> c     x  ==>       ==> c'
     |    |    |           \   |    |    |            |    |    |
     +----|----+            \  +----|----+            +----|----+
          v                  \      v                      v
          a'                  \==== b'                     a'

-}

respond-$
  :  (m : Functor (Sets 0ℓ) (Sets 0ℓ))
  -> {a' b b' c c' x x' : Set}
  -> Proxy (Functor.F₀ m) x' x b' b a'
  -> (b -> Proxy (Functor.F₀ m) x' x c' c b')
  -> Proxy (Functor.F₀ m) x' x  c' c a'
respond-$ m (pure a) fb = pure a
respond-$ m (effect  me cont[e]) fb 
  = effect me (\ e -> (respond-$ m  (cont[e] e) fb))
respond-$ m (request x' cont[x']) fb 
  = request x' (\ x' -> (respond-$ m (cont[x'] x') fb))
respond-$ m (respond  b  cont[b']) fb 
  = bind-proxy {m} (fb b) (\ b' -> respond-$ m (cont[b'] b') fb)


_/>/_
  :  {m : Functor (Sets 0ℓ) (Sets 0ℓ)}
  -> {a a' b b' c c' : Set}
  -> {x x' : Set}
  -> (a -> Proxy (Functor.F₀ m) x' x b' b a')
  -> (b -> Proxy (Functor.F₀ m) x' x c' c b')
  -> (a -> Proxy (Functor.F₀ m) x' x c' c a')
_/>/_ {m} fa fb a  = respond-$ m (fa a)  fb


