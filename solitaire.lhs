The Solitaire cipher (by Bruce Schneier, from Cryptonomicon by Neal Stephenson)
===============================================================================

This is written in Literate Haskell. You can run this file as any other Haskell
file.

> import Data.Char
> import Data.List
> import Data.Maybe

Deck representation
-------------------

The deck is (internally) represented as follows. Each card has a nominal value
between 1-13. In addition to this each suit has the following multipliers:
Clubs = 0, Diamonds = 1, Hearts = 2, Spades = 3. The A joker has the value 52,
and the B joker has the value 53. The order cards' values are calculated as:

suit * 13 + (value - 1)

giving a value in the range 0-53. Thus, a shuffled deck can be represented as a
list of 54 numbers between 0 and 53, where each number occurs exactly once.

> sortedDeck = take 54 [0..]
> jokerA = 52
> jokerB = 53
> jokerAIndex = fromJust . elemIndex jokerA
> jokerBIndex = fromJust . elemIndex jokerB

In addition to this, both the plaintext, ciphertext, and keystream can be
represented as a string a letters A-Z. A has the value 1 and Z the value 26.
However, internally, we use a zero-based representation to simplify modulo
calculations. However, because of this discrepancy, we get off-by-one errors
when adding, since e.g. A + A = B, but with our representation we would get
A + A = A unless we're careful. 

> fromLetters = map ((subtract 65) . ord)
> toLetters = map (chr . (+65))
> addMod26 a b = ((+1) . flip mod 26) (a + b) -- plaintext + keystream
> subMod26 a b = (flip mod 26 . (subtract 1)) (a - b) -- ciphertext - keystream

Encryption
----------

We take an input plaintext (only captial A-Z is allowed) together with a
keystream (of possibly inifinite length).

> encrypt plaintext = toLetters . map (uncurry addMod26) . zip (fromLetters plaintext)

Decryption
----------

We take an input ciphertext (only capital letters A-Z) together with a keystream
(of possible infinite length).

> decrypt ciphertext = toLetters . map (uncurry subMod26) . zip (fromLetters ciphertext)

Generating keystream
--------------------

We need to execute the following steps in order, to get a single keystream
number. This also modifies the state of the deck. Thus this function returns
both the new state and the output bit. I highly suspect that this can be done in
a very sexy way by using monads -- if only my Haskell skills were better.

> keystream = tail . map step6 . filter (<52) . map step5 . iterate (step4 . step3 . step2 . step1)

1. Find the A joker. Move it one card down (swap with the card beneath it).
   If the joker is at the bottom, move it just below the top card.

> step1 deck
>    | last deck == jokerA = head deck : jokerA : (init . tail) deck
>    | otherwise           = let start = take (jokerAIndex deck) deck
>                                swap  = deck !! (jokerAIndex deck + 1)
>                                end   = drop (jokerAIndex deck + 2) deck
>                            in start ++ swap : jokerA : end

2. Find the B joker. Move it two cards down. If the joker is the bottom card,
   move it just below the second card. If the joker is one up from the bottom,
   move it just below the top card.

> sublist from to = (take (to - from) . drop from)
> step2 deck
>    | last deck == jokerB          = take 2 deck ++ jokerB : (drop 2 . init) deck
>    | (last . init) deck == jokerB = head deck : jokerB : (tail . delete jokerB) deck
>    | otherwise                    = let start = take (jokerBIndex deck) deck
>                                         swap  = sublist (jokerBIndex deck + 1) (jokerBIndex deck + 3) deck
>                                         end   = drop (jokerBIndex deck + 3) deck
>                                     in start ++ swap ++ jokerB : end

3. Perform a triple cut. That is, swap the cards above the first joker with the
   cards below the second joker.

> firstJokerIndex deck = min (jokerAIndex deck) (jokerBIndex deck)
> lastJokerIndex deck = max (jokerAIndex deck) (jokerBIndex deck)
> firstJoker deck = deck !! (firstJokerIndex deck)
> lastJoker deck = deck !! (lastJokerIndex deck)
> step3 deck = let start  = take (firstJokerIndex deck) deck
>                  middle = sublist (firstJokerIndex deck) (lastJokerIndex deck + 1) deck
>                  end    = drop (lastJokerIndex deck + 1) deck
>              in end ++ middle ++ start

4. Perform a count cut. Look at the bottom card. Convert it to a number between
   1 and 53 (clubs, diamonds, hearts, spades order; 53 for both jokers). Count
   down from that number (from top of deck). Cut after card you counted to,
   but leaving the bottom card at the bottom. Note that this is the last step
   that actually modifies the deck.

> bottomValue = ((+1) . min 52 . last)
> step4 deck = drop (bottomValue deck) (init deck) ++ take (bottomValue deck) deck ++ [last deck]

5. Find output card. Look at top card. Convert it to a number from 1 to 53.
   Count down that many cards. Write the card after the one you counted to on a
   piece of paper. If you hit a joker, don't write anything down and start with
   step 1 again.

> topValue = ((+1) . min 52 . head)
> step5 deck = head $ drop (topValue deck) deck

6. Convert output card to a number [1,26], i.e. (card mod 26) + 1. However,
   in this implementation we internally assume the range [0,25] so we simply
   ignore this step here.

> step6 = id
> --step6 = (+1) . flip mod 26

Test cases
----------

Some of these are example keystreams for given decks. They are from the
appendix of Cryptonomicon.

> testEncryption = [testEncryption_1, testEncryption_2]
> testEncryption_1 = encrypt "DONOTUSEPC" (fromLetters "KDWUPONOWT") == "OSKJJJGTMW"
> testEncryption_2 = (encrypt "AAAAAAAAAA" $ keystream sortedDeck) == "EXKYIZSGEH"

> testDecryption = [testDecryption_1, testDecryption_2]
> testDecryption_1 = decrypt "OSKJJJGTMW" (fromLetters "KDWUPONOWT") == "DONOTUSEPC"
> testDecryption_2 = (decrypt "EXKYIZSGEH" $ keystream sortedDeck) == "AAAAAAAAAA"

First we note that the samples are over the output, i.e. before step 6, and
the jokers have not been filtered out.

> keystreamUnfiltered = tail . map step5 . iterate (step4 . step3 . step2 . step1)
> sample1 = take 16 $ keystreamUnfiltered sortedDeck

 > sample1 = take 10 $ keystreamUnfiltered sortedDeck
 > 4 49 10 53 24 8 51 44 6 4 33 20 39 19 34 42

The following are internal unit tests for various parts of the code.

> unitTestRunner = map errorCatcher $ intercalate [] [testStep1,testStep2,testSublist]
> errorCatcher False = error "Unit test failed"
> errorCatcher True = True

For step 1 of keystream generation.

> testStep1 = [testStep1_1, testStep1_2, testStep1_3]
> testStep1_1 = step1 [0,1,52,2,3,4,5] == [0,1,2,52,3,4,5]
> testStep1_2 = step1 [0,1,2,3,52] == [0,52,1,2,3]
> testStep1_3 = step1 [52,0,1,2,3,4,5] == [0,52,1,2,3,4,5]

For step 2 of keystream generation.

 > testStep2 = [testStep2_1, testStep2_2, testStep2_3, testStep2_4]

First we have the input, then the expected result.

> testStep2Cases = [([0,1,2,53,3,4,5,6], [0,1,2,3,4,53,5,6])
>                  ,([0,1,2,3,4,53],     [0,1,53,2,3,4])
>                  ,([0,1,2,3,53,4],     [0,53,1,2,3,4])
>                  ,([53,0,1,2,3],       [0,1,53,2,3])]
> testStep2 = map (uncurry (==)) $ zip (map (step2 . fst) testStep2Cases) (map snd testStep2Cases)

For step 3 of keystream generation.

> testStep3Cases = [([0,1,2,52,3,4,5,53,6,7], [6,7,52,3,4,5,53,0,1,2])
>                  ,([0,1,2,53,3,4,5,52,6,7], [6,7,53,3,4,5,52,0,1,2])
>                  ,([0,1,2,53,52,3,4,5]    , [3,4,5,53,52,0,1,2])
>                  ,([52,0,1,2,53,3,4,5]    , [3,4,5,52,0,1,2,53])
>                  ,([0,1,2,53,3,4,5,52]    , [53,3,4,5,52,0,1,2])
>                  ,([52,53,0,1,2,3,4,5]    , [0,1,2,3,4,5,52,53])
>                  ,([0,1,2,3,4,5,53,52]    , [53,52,0,1,2,3,4,5])]
> testStep3 = map (uncurry (==)) $ zip (map (step3 . fst) testStep3Cases) (map snd testStep3Cases)

For step 3 of keystream generation.

> testStep4Cases = [([7,6,53,52,1,30,31,32,4,5,11,13,21,10,8], [5,11,13,21,10,7,6,53,52,1,30,31,32,4,8])
>                  ,([10,11,12,13,14,15,16,17,18,19,3]       , [14,15,16,17,18,19,10,11,12,13,3])
>                  ,([10,11,12,13,0]                         , [11,12,13,10,0])
>                  ,([10,11,12,13,3],                          [10,11,12,13,3])]
> testStep4 = map (uncurry (==)) $ zip (map (step4 . fst) testStep4Cases) (map snd testStep4Cases)

Various helper functions

> testSublist = [testSublist_1,testSublist_2,testSublist_3,testSublist_4,testSublist_5]
> testSublist_1 = sublist 0 5 [0..5] == [0..4]
> testSublist_2 = sublist 0 0 [0..5] == []
> testSublist_3 = sublist 5 5 [0..5] == []
> testSublist_4 = sublist 0 1 [0..5] == [0]
> testSublist_5 = sublist 3 6 [0..5] == [3,4,5]
