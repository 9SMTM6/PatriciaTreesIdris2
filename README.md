# Project

This will hopefully end up being an implementation of a Radixtree specifically with radix 2 (?) AKA Patricia tree in as much as possible typed throught idris2.

My intention currently is to use some haskell implementation as reference where expedient, probably start with a less well typed port of one of these.

List of canditates in a quick session (sadly mostly production ready implementations that are performance optimized, which might not be a good fit for a language such as idris2, which I'm just getting used to):

* list-tries package https://hackage.haskell.org/package/list-tries-0.6.7/docs/Data-ListTrie-Patricia-Set.html
* fgl package https://hackage.haskell.org/package/fgl-5.8.2.0/docs/Data-Graph-Inductive-PatriciaTree.html
* haskell-ptree (pure source? still says its efficient) https://github.com/cpettitt/haskell-ptree
* bytestring-trie / text-trie package https://hackage.haskell.org/package/bytestring-trie https://hackage.haskell.org/package/text-trie
* radixtree package https://gitlab.com/transportengineering/radixtree

## Usecase

TBD

from hearesay its going to be used as standardlib for something else, possibly the effectful language that i forgot the name of?

So how important is speed when compared to 
* dependency size/having dependencies at all. IDK how well/if at all package management in idris2 works. Most haskell implementations appear to be using Data.ByteString (from [a package](https://hackage.haskell.org/package/bytestring-0.12.0.2/docs/Data-ByteString.html)), not Data.String or Data.Text (also from [a package](https://hackage.haskell.org/package/text-1.2.4.1/docs/Data-Text.html)). Not all of these have equivalent packages in idris2. theres a package for idris2 that claims to be equivalent of ByteString tho.
* ease of API use. As said above, most structures don't seem to use "Default" strings, as such this is probably reflected in their API, making use awkward when other strings were used before
* guaranteed correctness? IDK how easy it would be to implement speedier algorithms with complete guaranteed for correctness in idris2. Well, depending on the answers to other questions. UTF-8 can be nasty if you also want performance. With ByteString or similar its probably not too hard.

## API completeness

TBD (?)
