{-# OPTIONS --rewriting --type-in-type #-}
{- Note that there are two more options this time. The first
   (rewriting) is for adding new definitional equalities to agda.
   We will use this for the higher inductive type of propositional
   truncation.

   The second (type-in-type) should not usually be used, but helps
   simplify some things just for today. We won't use it again.
-}

open import PropositionsAsTypes
  {- The file PropositionsAsTypes contains several functions that we defined
     in the last two classes. -}
open import Equality
open import Bool

open import Agda.Primitive renaming (Level to ULevel)

module SetsandPropositionsSolutions where


{- Recall the definition of Σ types from last time. -}
record Σ  (A : Set ) (B : A → Set ) : Set  where
  constructor _,_
  field
    fst : A
    snd : B fst

{- A type is an hProposition or mere proposition if we can (uniformly) construct a path
   between any two points.
-}
is-hprop : Set → Set
is-hprop X = (x y : X) → (x == y)

{- Exercise 1: Show that ⊥ is an hProp -}
⊥-is-hprop : is-hprop ⊥
⊥-is-hprop x y = exfalso x
-- it is also possible to use absurd pattern matching


{- Exercise 2: Show that if X and Y are both hprops, then so is the pair type
   X ⊓ Y. -}

{- One way to do this is to first prove the lemma below. (This is the decode part
   of the encode decode method for pair types.)
-}
⊓-path : {X Y : Set} (xy xy' : X ⊓ Y) → (Pair.fst xy == Pair.fst xy') →
         (Pair.snd xy == Pair.snd xy') → (xy == xy')
⊓-path (.(Pair.fst xy') , .(Pair.snd xy')) xy' idp idp = idp

⊓-hprop : (X Y : Set) (xprop : is-hprop X) (yprop : is-hprop Y) →
          (is-hprop (X ⊓ Y))
⊓-hprop X Y xprop yprop xy xy' = ⊓-path xy xy' (xprop (Pair.fst xy) (Pair.fst xy'))
                                        (yprop (Pair.snd xy) (Pair.snd xy'))

{- An element of is-hprop is any dependent function f that
   assigns a path p from x to y for any x and y. A priori it would be
   reasonable to expect that there are other paths p from x to y that have
   nothing to do with with f x y. However, it turns out that we can
   prove that every path p from x to y is equal to f x y using a
   clever trick. As is often the case when working with identity
   types, the key point is to prove a more general statement by path
   induction (based path induction here), and deduce the result as a
   special case.
-}

{- Some of the functions that we proved last time have been copied into the file
   Equality.agda and imported so you can use them here.

   In particular ! p is the "reversal of p" so if p : x == y then ! p : y == x
   and we concatentate paths with ∙ so that if p : x == y and q : y == z then
   p ∙ q : x == z
-}

{- The following lemma might also be useful -}
!-cancel-l : {X : Set} {x y : X} (p q : x == y) → (p ∙ ((! p) ∙ q) == q)
!-cancel-l p idp = !-inv-r p


{- Exercise 3: Fill in the rest of the proof below. The two lemmas lemma1 and lemma2
   are there as hints. Try proving lemma1 first, then derive lemma2 as a special
   case, and then use lemma2 to prove the main lemma.

   You might find it useful to draw out the paths involved on paper (or see blackboard
   in class).

   There is another proof in the HoTT book (Lemma 3.3.4).
-}
hprop-lemma : {X : Set} (f : is-hprop X) (x y : X) (p : x == y) → (f x y == p)
hprop-lemma {X} f x y p = lemma2 ∙ !-cancel-l (f x y) p
  where
    {- The two useful lemmas have been put here as local definitions using the where keyword
       above. This ensures that we can use the same names lemma1 and lemma2 again elsewhere
       without getting any conflicts.
    -}
    lemma1 : (z : X) (q : y == z) → (f x z == f x y ∙ q)
    lemma1 z idp = idp

    lemma2 : (f x y == f x y ∙ (! (f x y) ∙ p))
    lemma2 = lemma1 y (! (f x y) ∙ p)

{- An h-set is a type where every identity type is an h-proposition. -}
is-hset : Set → Set
is-hset X = (x y : X) → is-hprop (x == y)

{- Note that the above lemma tells us that every hprop is an hset. -}
all-hprops-are-hsets : {X : Set} → (is-hprop X) → (is-hset X)
all-hprops-are-hsets f = λ x y → λ p q → ! (hprop-lemma f x y p) ∙ hprop-lemma f x y q

record is-contr  (X : Set) : Set  where
  constructor build-is-contr
  field
    center : X
    path : (x : X) → (x == center)

{- Exercise 4: Show that every contractible type is an hprop. -}
contr-implies-hprop : {X : Set} → (is-contr X) → (is-hprop X)
contr-implies-hprop c = λ x x' → is-contr.path c x ∙ ! (is-contr.path c x')

{- Exercise 5: Show that ⊤ is contractible -}
⊤-is-hprop : is-contr ⊤
⊤-is-hprop = build-is-contr unit (λ { unit → idp })
  {- This is using pattern matching in a lambda. It is also possible local definitions (let or where).
     See the agda documentation on Local Definitions for information about that.
  -}

{- Exercise 6: Show that for any element y of a type X, Σ X (λ x → x == y) is contractible. -}
contractible-paths :  {X : Set} (y : X) → is-contr (Σ X (λ x → x == y))
contractible-paths x = build-is-contr (x , idp) λ { (.x , idp) → idp }
  {- Again this is a quick solution using pattern matching with lambda, but can also be done
     using local definitions. There is another, less direct but in some ways more
     informative proof in the HoTT book Lemma 3.11.8, this using the encode decode method
     for Σ-types together with a similar explicit description for transport in path types. -}

{- Recall from last time that we say two functions f and g are homotopic
   (f ∼ g) if f a == g a for all a
-}
_∼_ : {A : Set} {B : A → Set} (f g : (a : A) → B a) → Set
_∼_ {A} f g = (a : A) → f a == g a

{- Also recall from last time function extensionality. We will only need the function
   funext rather than the whole quasi-inverse.
-}
postulate
  funext : {X : Set} {Y : X → Set} (f g : (x : X) → Y x) → (f ∼ g) → (f == g)


{- Exercise 7: Suppose that Y is a type dependent on X and that for every x, Y x is
   an hprop. Show that the type of dependent functions (x : X) → Y x is also an
   hprop. You may use function extensionality.
-}
hprop-dep-prod : {X : Set} {Y : X → Set} (ihp : (x : X) → is-hprop (Y x)) →
                 is-hprop ((x : X) → Y x)
hprop-dep-prod ihp = λ f g → funext f g λ x → ihp x (f x) (g x)

{- Exercise 8: Prove that is-hprop is itself an hprop (i.e. a type X can only be
   an hprop in one way
-}
hprop-is-hprop : {X : Set} → (is-hprop (is-hprop X))
hprop-is-hprop = λ ihp1 ihp2 → funext ihp1 ihp2 λ x → funext (ihp1 x) (ihp2 x)
                   (λ y → all-hprops-are-hsets ihp2 x y (ihp1 x y) (ihp2 x y))

{- Exercise 9: Prove that is-hset is an hprop. -}
is-hset-is-hprop : {X : Set} → (is-hprop (is-hset X))
is-hset-is-hprop ihs1 ihs2 = funext ihs1 ihs2 (λ x → funext (ihs1 x) (ihs2 x)
                                    (λ y → hprop-is-hprop (ihs1 x y) (ihs2 x y)))

{- We can make exercise 10 easier by proving an extra lemma along the same lines
   as above.
-}
contr-has-contr-paths : {X : Set} → (is-contr X) → ((x y : X) → is-contr (x == y))
contr-has-contr-paths c x y = let ihp = λ x' y' → (contr-implies-hprop c x' y')
                              in build-is-contr (ihp x y) λ p → all-hprops-are-hsets ihp x y p _


{- Exercise 10: Prove that is-contr is an hprop.
   Hint: You might find it easier to first prove the lemma, and then use the lemma,
   funext, and one of the functions above to prove the main result.
 -}
is-contr-is-hprop : {X : Set} → (is-hprop (is-contr X))
is-contr-is-hprop {X} x x' = lemma x x' q
                                   (funext _ _ λ z → contr-implies-hprop (contr-has-contr-paths x' z _) _ _)
  where
    lemma : (c c' : is-contr X) (q : is-contr.center c == is-contr.center c')
            (r : (λ x → is-contr.path c x ∙ q) == λ x → is-contr.path c' x) → (c == c')
    lemma (build-is-contr .(is-contr.center c') .(is-contr.path c')) c' idp idp = idp

    q : (is-contr.center x == is-contr.center x')
    q = (is-contr.path x' (is-contr.center x))

{- In general we use the word 'is' to refer to types that are (or that we expect
   to be) mere propositions.
-}


{- Fix a function f : X → Y -}
module _  {X Y : Set } (f : X → Y) where

  {- Recall that last time we defined quasi inverse (qinv) below. -}
  record qinv : Set  where
    field
      g : Y → X
      f-g : (y : Y) → (f (g y) == y)
      g-f : (x : X) → (g (f x) == x)

  {- We then said that f is an equivalence if it has a quasi inverse. -}

  {- In set theory we are accustomed to each function having at most one inverse.
     This is not true for qinv. However, by choosing the definition of inverse
     carefully we can ensure that every function has at most one inverse.
  -}


  {- We first define homotopy fiber, or hfiber. An element of hfiber y
     consists of a point x of X together with a path p from f x to y.
  -}
  hfiber : (y : Y) → Set
  hfiber y = Σ X (λ x → f x == y)

  {- An inverse to f is a proof that every fiber is contractible. -}
  inverse : Set
  inverse = (y : Y) → is-contr (hfiber y)

  {- Exercise 11: show that if f has an inverse then it has a quasi inverse. -}
  {- Note g-f is quite tricky. You might find it helpful to draw out what it
     looks like on paper first.
  -}
  inverse-qinv : inverse → qinv
  inverse-qinv inv = record { g = λ y → Σ.fst (is-contr.center (inv y))
                            ; f-g = λ y → Σ.snd (is-contr.center (inv y))
                            ; g-f = λ x → ap Σ.fst (! (is-contr.path (inv (f x)) (x , idp))) }
  {- Note that (x , idp) is an element of the fiber of f x, and so is equal to
     (is-contr.center (inv (f x))) via is-contr.path. We use ! to make the path
     go the right way round, and then ap to get a path between the first components.
     (The first component of the hfiber is the element of X).
  -}

  {- The converse is also true, but it is harder. We will see it next time.
     Hence inverse and qinv are logically equivalent (but not equivalent,
     because different quasi inverses might get mapped to the same inverse).
  -}

  {- We can use our earlier result to show that inverse is an hprop. In other
     words every function has at most one inverse.
     Exercise 12: Do this.
  -}
  inverse-is-hprop : is-hprop inverse
  inverse-is-hprop = hprop-dep-prod (λ y → is-contr-is-hprop)

  {- If f has a (necessarily unique) inverse, we say it is an equivalence. Note that
     since inverse is unique we think of this as a property of the function f rather
     than extra structure.
  -}
  is-equiv : Set
  is-equiv = inverse

{- Given types X and Y, we define the type of equivalences from X to Y
   (X ≃ Y, written X \simeq Y), to be pairs consisting of a function f
   and a proof that f is an equivalence.
-}
record Equiv (X Y : Set ) : Set  where
  field
    f : X → Y
    f-is-equiv : is-equiv f

_≃_ : (X Y : Set) → Set
X ≃ Y = Equiv X Y

{- We now work towards the most important axiom of homotopy type theory: univalence.
   In order to do this properly we will need universe levels, which will be covered
   next time.

   For now, to keep things simple we have enabled the option type-in-type (this is
   bad and should not usually be done).
-}

{- Recall that we refer to the identity function on a type X as f. -}
idf :  (X : Set ) → X → X
idf X x = x

{- We can prove that the identity function is an equivalence using a lemma from earlier. -}
idf-is-equiv :  {X : Set } → (is-equiv (idf X))
idf-is-equiv = contractible-paths

{- We write the resulting equivalence like this -}
idf-equiv : {X : Set} → X ≃ X
idf-equiv {X} = record { f = idf X  ; f-is-equiv = idf-is-equiv }

{- Since the identity function is an equivalence, we have a canonical map
   from proofs that X and Y are equal to proofs that X and Y are equivalent.
-}
idtoequiv : (X Y : Set) → (X == Y) → (X ≃ Y)
idtoequiv X Y idp = record { f = idf _ ; f-is-equiv = idf-is-equiv }

{- The univalence axiom states that this map is itself an equivalence. -}
postulate
  univalence-axiom : (X Y : Set) → is-equiv (idtoequiv X Y)

{- In particular we get the function ua below. -}
ua : (X Y : Set) → (X ≃ Y) → (X == Y)
ua X Y = qinv.g (inverse-qinv (idtoequiv X Y) (univalence-axiom X Y))

{- More on univalence next time! -}


{- Homework -}

{- (a) We are going to prove that Set is not an hset. First prove that the function
   not from Bool to Bool has a quasi inverse.
-}

not : Bool → Bool
not true = false
not false = true

not-qinv : qinv not
not-qinv = record { g = not
                  ; f-g = λ { false → idp ; true → idp}
                  ; g-f = λ {false → idp ; true → idp} }
{- This solution uses pattern matching in lambdas to save typing, but it
   is also possible to just write out f-g and g-f as separate functions. -}


{- (b) Prove that not is not equal to the identity function on Bool -}

{- You might find it helpful to use the following functions that we have
   defined in class. They all appear in the files imported at the top of
   this file, so you can use them.

   true-≠-false : true ≠ false

   modus-tollens : {X Y : Set} → (X → Y) → (¬ Y → ¬ X)

   app= : {A : Set} {B : A → Set} (f g : (a : A) → B a) →
           (f == g) → ((a : A) → f a == g a)
-}

not-≠-idf : not ≠ (idf Bool)
not-≠-idf = modus-tollens (λ p → app= not (idf Bool) p false) true-≠-false
  -- If not was equal to idf, then not false = true would be equal to false.

{- (c) Prove that the quasi inverse of any function f is always injective.
-}
qinv-is-inj : {X Y : Set} (f : X → Y) (inv : qinv f) →
              (x y : Y) → (p : qinv.g inv x == qinv.g inv y) → (x == y)
qinv-is-inj f inv x y p = ! (qinv.f-g inv x) ∙ (ap f p ∙ qinv.f-g inv y)
{- By sketching it out on paper we can see that this is the composition
   of three paths. Each time we fill in a path it tells us what on of the
   end points of the neighbouring path should be.
-}


{- Hint: As for some of the exercises, you might find this easier if you
   sketch out the paths you know about on paper first.
-}

{- Next time we will show that qinv and inverse are logically equivalent.
   For now, we will just assume the non trivial direction as an axiom.
-}
postulate
  qinv-inverse : {X Y : Set} (f : X → Y) → (qinv f) → (inverse f)

{- We will write the resulting equivalence as not-equiv -}

not-equiv : Bool ≃ Bool
not-equiv = record { f = not ; f-is-equiv = qinv-inverse not not-qinv }

{- Using the univalence axiom we get two paths p and q from Bool to Bool -}

p : Bool == Bool
p = ua Bool Bool idf-equiv

q : Bool == Bool
q = ua Bool Bool not-equiv

{- (d) Prove that these two paths are not equal -}
p≠q : p ≠ q
p≠q = modus-tollens (λ α → ap (Equiv.f) (qinv-is-inj (idtoequiv Bool Bool)
      (inverse-qinv (idtoequiv Bool Bool) (univalence-axiom Bool Bool))
        not-equiv idf-equiv (! α))) not-≠-idf
{- It is possible to do the whole thing at once, as above, but it can be easier
   to break it down a bit a time, particularly by showing that idf-equiv ≠ not-equiv first, and
   then applying qinv-is-inj. Note that for this to work depends on the particular definition
   of ua, in particular that it was defined from inverse-qinv.
-}



{- (e) Deduce that Set is not a set -}
Set-not-hset : ¬ (is-hset Set)
Set-not-hset = modus-tollens (λ sethset → sethset Bool Bool p q) p≠q


{- Bonus question -}

{- So far we have always included the option --without-K in every file. We can
   now see why this is. Delete --without-K from the line at the top
   of this file, so it reads {-# OPTIONS --rewriting --type-in-type #-}.
-}

{- Axiom K states that every type is an hset. Show that without the
   --without-K option this can be done using pattern matching.
-}
K : (X : Set) → (is-hset X)
K X x .x idp idp = idp
{- This kind of pattern matching is acceptable in the presence of --without-K.
   Hopefully the above line looks strange to you now.
-}

{- Use this to construct an element of ⊥ -}
contradiction : ⊥
contradiction = Set-not-hset (K Set)
