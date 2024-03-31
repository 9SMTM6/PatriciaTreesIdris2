import Data.Vect
import Decidable.Equality

data PrefixTree : (len : Nat) -> (tVal : Type) -> Type where
    Leaf : (val : tVal) -> PrefixTree 0 tVal
    Left : (lTrie : PrefixTree len tVal) -> PrefixTree (S len) tVal
    Right : (rTrie : PrefixTree len tVal) -> PrefixTree (S len) tVal
    Both : (lTrie : PrefixTree len tVal) -> (rTrie : PrefixTree len tVal) -> PrefixTree (S len) tVal

BoolDirection: Bool -> PrefixTree len tVal -> PrefixTree (S len) tVal
BoolDirection False = Left
BoolDirection True = Right

BD : Bool -> PrefixTree len tVal -> PrefixTree (S len) tVal
BD = BoolDirection

Key : (len: Nat) -> Type
Key len = Vect len Bool

-- testReplace: (x=y) -> (p1 x) -> (p1 y)
-- testReplace a b = replace a b

-- required for decEqCong
-- which is required because idris2 doesnt support rewrite with dependent types yet:
-- https://github.com/idris-lang/Idris2?tab=readme-ov-file#things-still-missing
-- I dont remember this being said in the lecture and it for sure wasnt mentioned in the reference documentation 
-- as it really should...
-- Wasted a few of my hours.
-- btw: I'm basically just copying over implementations from idris2 source now.
-- I trust in this system to catch errors, 
-- sometimes (particularly in the impl for DecEq) I've just got the glint of an idea of whats happening.
-- I've done a bit of effort to experimentally test correctness of copied code.
total
implementation
Injective Leaf where
    injective Refl = Refl

total
implementation
Injective Main.Left where
    injective Refl = Refl

total
implementation
Injective Main.Right where
    injective Refl = Refl

total
implementation
Biinjective Main.Both where
    biinjective Refl = (Refl, Refl)

total
implementation
DecEq tVal => DecEq (PrefixTree len tVal) where
    decEq (Leaf val) (Leaf val1) = decEqCong $ decEq val val1
    decEq (Left lTrie) (Left lTrie1) = decEqCong $ decEq lTrie lTrie1
    decEq (Right rTrie) (Right rTrie1) = decEqCong $ decEq rTrie rTrie1
    decEq (Both lTrie rTrie) (Both lTrie1 rTrie1) = decEqCong2 (decEq lTrie lTrie1) (decEq rTrie rTrie1)
    decEq (Left lTrie) (Right rTrie) = No $ \case Refl impossible
    decEq (Left lTrie) (Both x rTrie) = No $ \case Refl impossible
    decEq (Right rTrie) (Left lTrie) = No $ \case Refl impossible
    decEq (Right rTrie) (Both lTrie x) = No $ \case Refl impossible
    decEq (Both lTrie rTrie) (Left x) = No $ \case Refl impossible
    decEq (Both lTrie rTrie) (Right x) = No $ \case Refl impossible

-- todo: introduce errors once tests are established

-- IDK if I did this syntax properly
-- {0 len: Nat} ->
total
singleton : (key: Key len) -> (val: tVal) -> PrefixTree len tVal
singleton [] val = Leaf val
singleton (x :: xs) val = (BD x) (singleton xs val)

total
insert : Key len -> tVal -> PrefixTree len tVal -> PrefixTree len tVal
-- termination
insert [] val trie = Leaf val
-- termination: with singleton
insert (False::xs) val (Right rTrie) = Both (singleton xs val) rTrie
insert (True::xs) val (Left lTrie) = Both lTrie (singleton xs val)
-- recursion: sparse
insert (False::xs) val (Left lTrie) = Left (insert xs val lTrie)
insert (True::xs) val (Right rTrie) = Right (insert xs val rTrie)
-- recursion: dense
insert (False::xs) val (Both lTrie rTrie) = Both (insert xs val lTrie) rTrie
insert (True::xs) val (Both lTrie rTrie) = Both lTrie (insert xs val rTrie)

total
lookup : Key len -> PrefixTree len tVal -> Maybe tVal
-- termination
lookup [] (Leaf val) = Just val
lookup (False::xs) (Right _) = Nothing
lookup (True::xs) (Left _) = Nothing
-- recursion: sparse
lookup (False::xs) (Left lTrie) = lookup xs lTrie
lookup (True::xs) (Right rTrie) = lookup xs rTrie
-- recursion: dense
lookup (x::xs) (Both lTrie rTrie) = Main.lookup xs (case x of
        False => lTrie
        True => rTrie
    )

total
||| "last" element (so the elements from the 2nd prefix tree) will win
||| so its value will be in the resulting set
-- todo: type-testcase for that
union : PrefixTree len tVal -> PrefixTree len tVal -> PrefixTree len tVal
-- termination
union (Leaf _) (Leaf val1) = Leaf val1
union (Left lTrie) (Right rTrie) = Both lTrie rTrie
union (Right rTrie) (Left lTrie) = Both lTrie rTrie
-- recursion: same
union (Left lTrie0) (Left lTrie1) = Left (union lTrie0 lTrie1)
union (Right rTrie0) (Right rTrie1) = Right (union rTrie0 rTrie1)
union (Both lTrie0 rTrie0) (Both lTrie1 rTrie1) = Both (union lTrie0 lTrie1) (union rTrie0 rTrie1)
-- recursion: different (one must be Both, otherwise termination)
union (Left lTrie0) (Both lTrie1 rTrie1) = Both (union lTrie0 lTrie1) rTrie1
union (Right rTrie0) (Both lTrie1 rTrie1) = Both lTrie1 (union rTrie0 rTrie1)
union (Both lTrie0 rTrie0) (Left lTrie1) = Both (union lTrie0 lTrie1) rTrie0
union (Both lTrie0 rTrie0) (Right rTrie1) = Both lTrie0 (union rTrie0 rTrie1)

total
delete: Key len -> PrefixTree len tVal -> Maybe (PrefixTree len tVal)
delete [] (Leaf _) = Nothing
delete (False::xs) remains@(Right _) = Just remains
delete (True::xs) remains@(Left _) = Just remains
delete (False::xs) (Left trie) = map Left (delete xs trie)
delete (True::xs) (Right trie) = map Right (delete xs trie)
delete (False::xs) (Both lTrie rTrie) = do
    let lDeleted = delete xs lTrie
    Just (
        case lDeleted of
            Nothing => Right rTrie
            Just lDelInner => Both lDelInner rTrie
        )
delete (True::xs) (Both lTrie rTrie) = do
    let rDeleted = delete xs rTrie
    Just (
        case rDeleted of
            Nothing => Left lTrie
            Just rDelInner => Both lTrie rDelInner
        )

total
-- todo: OUTDATED
-- explanation return type: an intersection might be smaller, importantly it might be entirely empty.
-- we could introduce an empty tree marker,
-- but that would mean that the tree can end up in a messy state with empty trees
-- at the ends of long prefixes.
-- Thats hugely inefficient and makes things more messy to implement.
-- Thus we want to delete parts going nowhere.
-- But in that case the resulting tree might be smaller in depth (len).
-- thus we need to be able to go smaller.
-- But idris2 doesnt like len coming out of nowhere, understandibly.
-- With dependent pairs the len will be an explicit part of the return type,
-- in ways that both the code and type system can read its value, which idris likes.
-- The parts with Fin just record that the resulting tree may be smaller, not larger in key len.
||| "last" element (so the elements from the 2nd prefix tree) will win
||| so its value will be in the resulting set
intersection : PrefixTree len tVal -> PrefixTree len tVal -> Maybe (PrefixTree len tVal)
intersection (Right _) (Left val1) = Nothing
intersection (Left _) (Right val1) = Nothing
intersection (Leaf _) winner@(Leaf val1) = Just winner
intersection (Both lTrie0 _) (Left lTrie1) = map Left (intersection lTrie0 lTrie1)
intersection (Both _ rTrie0) (Right rTrie1) = map Right (intersection rTrie0 rTrie1)
intersection (Left lTrie0) (Both lTrie1 _) = map Left (intersection lTrie0 lTrie1)
intersection (Right rTrie0) (Both _ rTrie1) = map Right (intersection rTrie0 rTrie1)
intersection (Right rTrie0) (Right rTrie1) = map Right (intersection rTrie0 rTrie1)
intersection (Left lTrie0) (Left lTrie1) = map Left (intersection lTrie0 lTrie1)
intersection (Both lTrie0 rTrie0) (Both lTrie1 rTrie1) = do
    lInt <- (intersection lTrie0 lTrie1)
    rInt <- (intersection rTrie0 rTrie1)
    Just (Both lInt rInt)

-- hlp_thm_lookupLeafSingleton: (lookup [] (singleton [] val)) = Just val
-- hlp_thm_lookupLeafSingleton = Refl

-- I seem unable to use these kind of proofs productively...
-- hlp_thm_followSingletonKeyStep : (x: Bool) -> (lookup (x::xs) (singleton (x::ys) val)) = (lookup xs (singleton ys val))
-- hlp_thm_followSingletonKeyStep False = Refl
-- hlp_thm_followSingletonKeyStep True = Refl

-- hlp_thm_whatever: {1 val :tVal} -> (lookup [] (singleton [] val)) = (lookup [] (Leaf val))
-- hlp_thm_whatever = cong2 lookup
-- total

thm_singletonContainsPair : (key: Key len) -> Main.lookup key (singleton key val) = Just val
thm_singletonContainsPair [] = Refl
-- hlp_thm_lookupLeafSingleton
thm_singletonContainsPair (False :: xs) = thm_singletonContainsPair xs
thm_singletonContainsPair (True :: xs) = thm_singletonContainsPair xs

hlp_thm_followSingletonKeyStep: (keyExt: Bool) -> (BD keyExt) (singleton key val) = singleton (keyExt::key) val
hlp_thm_followSingletonKeyStep _ = Refl

hlp_thm_mapNothing : map (BD newX) (the (Maybe (PrefixTree _ _)) Nothing) = Nothing
hlp_thm_mapNothing = Refl

-- thm_what: (newX: Bool) -> (map (BD newX) (delete xs (singleton xs val))) = (delete (newX::xs) (singleton (newX::xs) val))
-- thm_what False = Refl
-- thm_what True = Refl

-- stepUpKeyLen : (newX: Bool) -> (xs: Key len) -> delete xs (singleton xs val) = Nothing -> map (BD newX) (delete xs (singleton xs val)) = Nothing
-- stepUpKeyLen _ [] _ = Refl
-- stepUpKeyLen False (x :: xs) prf = ?stp --stepUpKeyLen x xs prf
-- stepUpKeyLen True (x :: xs) prf = ?stepup_5

thm_emptySingleton : {val: tVal} -> (key: Key len) -> Main.delete key (singleton key val) = Nothing
thm_emptySingleton [] = Refl
thm_emptySingleton (False :: xs) = cong (map Left) $ thm_emptySingleton xs
thm_emptySingleton (True :: xs) = cong (map Right) $ thm_emptySingleton xs
-- (map Main.Left (Main.delete xs (singleton xs val)))
--  ?empt --stepUpKeyLen False xs (thm_emptySingleton xs)

-- hlp_followSingletonKey: (lookup (x::xs) (singleton (x::ys) val)) -> (lookup xs (singleton ys val))

total
thm_lookupInserted : DecEq tVal => {1 len: Nat} -> (key: Key len) -> (val: tVal) -> (trie: PrefixTree len tVal) -> lookup key (insert key val trie) = Just val
-- idris can prove base case itself
thm_lookupInserted [] val (Leaf x) = Refl
-- recursion
thm_lookupInserted (False :: xs) val (Left lTrie) = thm_lookupInserted xs val lTrie
thm_lookupInserted (False :: xs) val (Both lTrie rTrie) = thm_lookupInserted xs val lTrie
thm_lookupInserted (True :: xs) val (Right rTrie) = thm_lookupInserted xs val rTrie
thm_lookupInserted (True :: xs) val (Both lTrie rTrie) = thm_lookupInserted xs val rTrie
-- refer to other proof (todo: why cant it discover this proof automatically? That made me go in circles a bit)
thm_lookupInserted (False :: xs) val (Right rTrie) = thm_singletonContainsPair xs
thm_lookupInserted (True :: xs) val (Left lTrie) = thm_singletonContainsPair xs

thm_insertSingletonUnionEquivalence : (key: Key len) -> (trie: PrefixTree len tVal) -> union (singleton key val) trie = insert key val trie
thm_insertSingletonUnionEquivalence [] (Leaf x) = ?what_4
thm_insertSingletonUnionEquivalence key (Left lTrie) = ?what_1
thm_insertSingletonUnionEquivalence key (Right rTrie) = ?what_2
thm_insertSingletonUnionEquivalence key (Both lTrie rTrie) = ?what_3

-- -- theoreme das etwas gelöschtes weg ist
-- thm_deleteDeletes : (env: Void) -> delete key (insert key val trie) = trie


ex = singleton ([False, True, False]) "hello world"

ex1 = insert ([False, True, True]) "inserted" ex

val: (n : Nat ** Vect n Nat)
val = (3 ** [4,3,5])

ex2 = Both (Both (Left (Leaf 2)) (Right (Leaf 3))) (Left (Right (Leaf 3)))

-- todo theoreme

-- main : IO ()
-- main = do
--     let ex = singleton ([False, True, False]) "hello world"
--     printLn ex
--     pure ()
