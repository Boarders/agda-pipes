module Pipes where

open import Categories.Functor
open import Categories.Category.Instance.Sets
open import Level
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality

open ≡-Reasoning

postulate
  extensionality : ∀ {l l'} {S : Set l}{T : Set l'}
                   {f g : (x : S) -> T} ->
                   ((x : S) -> f x ≡ g x) ->
                   f ≡ g

_≡$_ : ∀ {l l'}{A : Set l} {B : A → Set l'} {f g : (x : A) → B x} →
       f ≡ g → (x : A) → f x ≡ g x
refl ≡$ x = refl

_$≡_ : ∀ {l l'}{A : Set l} {B : Set l'} {x y : A} →
       (f : A -> B) -> x ≡ y → f x ≡ f y
f $≡ refl = refl

{-

 Upstream | Downstream
     +---------+
     |         |
 a' <==       <== b'
     |         |
 a  ==>       ==> b
     |    |    |
     +----|----+
          v
          r

-}
data Proxy 
       (m : Set -> Set)
       (a' a b' b : Set)
       (r : Set)  : Set₁ where
  pure    : r -> Proxy m a' a b' b r
  effect  : ∀{x} -> m x ->  (x  -> Proxy m a' a b' b r) -> Proxy m a' a b' b r
  request : a'          ->  (a  -> Proxy m a' a b' b r) -> Proxy m a' a b' b r
  respond : b           ->  (b' -> Proxy m a' a b' b r) -> Proxy m a' a b' b r


1ℓ : Level
1ℓ = Level.suc 0ℓ

map-proxy 
  :  (m : Functor (Sets 0ℓ) (Sets 0ℓ))
  -> {a' a b' b : Set}
  -> {r r' : Set}
  -> (f : r -> r')
  -> Proxy (Functor.F₀ m) a' a b' b r -> Proxy (Functor.F₀ m) a' a b' b r'
map-proxy m f (pure r) = pure (f r)
map-proxy m f (effect mx cont[x])
  = effect mx (map-proxy m f ∘ cont[x])
map-proxy m f (request a' cont[a])
  = request a' ((map-proxy m f) ∘ cont[a])
map-proxy m f (respond b cont[b']) 
  = respond b ((map-proxy m f) ∘ cont[b'])


bind-proxy
  :  {m : Functor (Sets 0ℓ) (Sets 0ℓ)}
  -> {a' a b' b : Set}
  -> {r r' : Set}
  -> Proxy (Functor.F₀ m) a' a b' b r
  -> (r -> Proxy (Functor.F₀ m) a' a b' b r')
  -> Proxy (Functor.F₀ m) a' a b' b r'
bind-proxy {m} (pure r) cont[r] = cont[r] r
bind-proxy {m} (effect mx  cont[x])  cont[r] 
  = effect mx  \ x  -> bind-proxy{m} (cont[x] x)   cont[r]
bind-proxy {m} (request a' cont[a])  cont[r] 
  = request a' \ a  -> bind-proxy{m} (cont[a] a)   cont[r]
bind-proxy {m} (respond b  cont[b']) cont[r] 
  = respond b  \ b' -> bind-proxy{m} (cont[b'] b') cont[r]

_p>>=_
  :  {m : Functor (Sets 0ℓ) (Sets 0ℓ)}
  -> {a' a b' b : Set}
  -> {r r' : Set}
  -> Proxy (Functor.F₀ m) a' a b' b r
  -> (r -> Proxy (Functor.F₀ m) a' a b' b r')
  -> Proxy (Functor.F₀ m) a' a b' b r'
_p>>=_ {m} = bind-proxy {m}

id-law  
  :  (m : Functor (Sets 0ℓ) (Sets 0ℓ))
  -> {a' a b' b : Set}
  -> {r : Set}
  -> (p : Proxy (Functor.F₀ m) a' a b' b r)
  -> map-proxy m (λ r -> r) p ≡ p
id-law m (pure r) = refl
id-law m (effect mx cont[x])
  = begin 
      effect mx (\ x -> map-proxy m (\r -> r) (cont[x] x))
        ≡⟨ effect mx $≡ (extensionality (λ x -> id-law m (cont[x] x))) ⟩
      (effect mx cont[x]) ∎
id-law m (request t[a'] cont[a])
  = begin 
      request t[a'] (\ a -> map-proxy m (\r -> r) (cont[a] a))
        ≡⟨ request t[a'] $≡ (extensionality (λ a -> id-law m (cont[a] a))) ⟩
      (request t[a'] cont[a]) ∎
id-law m (respond t[b] cont[b'])
  = begin 
      respond t[b] (\ b' -> map-proxy m (\r -> r) (cont[b'] b'))
        ≡⟨ respond t[b] $≡ (extensionality (λ b' -> id-law m (cont[b'] b'))) ⟩
      (respond t[b] cont[b']) ∎ 


assoc-law
 :  {R S T : Set} (f : R → S) (g : S → T) {a a' b b' : Set}
 -> (m : Functor (Sets 0ℓ) (Sets 0ℓ))
 -> (p : Proxy (Functor.F₀ m) a' a b' b R)
  -> map-proxy m (λ r → g (f r)) p ≡
      map-proxy m g (map-proxy m f p)
assoc-law _ _ m (pure r) = refl
assoc-law f g m (effect mx cont[x])
  = begin 
      (effect mx (\ x -> map-proxy m (\ r -> g (f r)) (cont[x] x))
         ≡⟨ effect mx $≡ 
              extensionality (\ x -> assoc-law f g m (cont[x] x)) ⟩
      effect mx (λ x → map-proxy m g (map-proxy m f (cont[x] x))) ∎)
assoc-law f g m (request a' cont[a]) 
  = begin 
      (request a' (\ a -> map-proxy m (\ r -> g (f r)) (cont[a] a))
         ≡⟨ request a' $≡ 
              extensionality (\ a -> assoc-law f g m (cont[a] a)) ⟩
      request a' (λ a → map-proxy m g (map-proxy m f (cont[a] a))) ∎)
assoc-law f g m (respond b cont[b']) 
  = begin 
      (respond b (\ b' -> map-proxy m (\ r -> g (f r)) (cont[b'] b'))
         ≡⟨ respond b $≡ 
              extensionality (\ b' -> assoc-law f g m (cont[b'] b')) ⟩
      respond b (λ b' → map-proxy m g (map-proxy m f (cont[b'] b'))) ∎)

resp-eq : {a a' b b' : Set} {A B : Set} {f g : A → B} →
      ({x : A} → f x ≡ g x) →
      (m : Functor (Sets 0ℓ) (Sets 0ℓ))
      (p : Proxy (Functor.F₀ m) a' a b' b A) →
      map-proxy m f p ≡ map-proxy m g p
resp-eq {f = f} {g = g} pointwiseEq m (pure r) 
  = begin 
      (pure (f r)) 
    ≡⟨ pure $≡ (pointwiseEq {r}) ⟩ 
      (pure (g r)) 
    ∎
resp-eq {f = f} {g = g} pointwiseEq m (effect mx cont[x])
  = begin 
       effect mx (\ x -> map-proxy m f (cont[x] x)) 
    ≡⟨ effect mx $≡ (extensionality (\ x -> resp-eq pointwiseEq m (cont[x] x))) ⟩
       effect mx (\ x -> map-proxy m g (cont[x] x)) 
    ∎
resp-eq {f = f} {g = g} pointwiseEq m (request a' cont[a])
  = begin 
       request a' (\ a -> map-proxy m f (cont[a] a)) 
    ≡⟨ request a' $≡ (extensionality (\ a -> resp-eq pointwiseEq m (cont[a] a))) ⟩
       request a' (\ a -> map-proxy m g (cont[a] a)) 
    ∎
resp-eq {f = f} {g = g} pointwiseEq m (respond b cont[b'])
  = begin 
       respond b (\ b' -> map-proxy m f (cont[b'] b')) 
    ≡⟨ respond b $≡ (extensionality (\ b' -> resp-eq pointwiseEq m (cont[b'] b'))) ⟩
       respond b (\ b' -> map-proxy m g (cont[b'] b')) 
    ∎

proxy-F : 
     (m : Functor (Sets 0ℓ) (Sets 0ℓ))
  -> (a' a b' b : Set)
  -> Functor (Sets 0ℓ) (Sets 1ℓ)
proxy-F m-func a' a b' b = 
  record
    { F₀ = Proxy m₀ a' a b' b
    ; F₁ = map-proxy m-func
    ; identity = id-law m-func _
    ; homomorphism = assoc-law _ _ m-func _
    ; F-resp-≈ = λ eq -> resp-eq eq m-func _
    }
  where
    open Functor m-func renaming (F₀ to m₀)


