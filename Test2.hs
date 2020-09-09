{-# OPTIONS_GHC -Wno-tabs #-}
{-# LANGUAGE GADTs, PolyKinds, KindSignatures, DataKinds, TypeOperators, RankNTypes, ScopedTypeVariables #-}

module Test2 where

import Data.Kind
import Control.Lens

data Prompt = Prompt Type Prompts
type Prompts = [Prompt]

data Cont r (ps1 :: Prompts) (ps2 :: Prompts) a

-- instance Functor (Cont r ps) where
-- instance Applicative (Cont r ps) where
-- instance Monad (Cont r ps) where

inFrame ::
	Cont r ('Prompt a ps2 ': ps1) ('Prompt a ps2 ': ps2) a ->
	Cont r ps1 ps2 a
inFrame b = _

data PromptRef p (ps' :: Prompts) (ps :: Prompts) where
	PRHead :: PromptRef p ps (p ': ps)
	PRTail :: PromptRef p ps' ps -> PromptRef p ps' (p' ': ps)

jumpOut ::
	PromptRef ('Prompt t p_ps) pr_ps1 ps1 ->
	(
		(a -> Cont r ps2 ('Prompt t p_ps ': p_ps) rt) ->
		Cont r pr_ps1 p_ps jt
	) ->
	Cont r ps1 ps2 a
jumpOut pr f = _

{-
	do
		-- []
		inFrame @"a" $ do
			-- ["a"]
			inFrame @"b" $ do
				-- ["b", "a"]
				() <- jumpOut 0 $ \kb -> do
					-- ["a"]
					() <- jumpOut 0 $ \ka -> do
						-- []
						inFrame @"c" $ ka ()
						-- []
					-- ["c"]
				-- ["c"]
			-- ["c"]

	do
		-- [] - 1
		inFrame @"a" $ do
			-- ["a"] - 2
			() <- jumpOut 0 $ \ka -> do
				-- [] - 3
				inFrame @"b" $ do
					-- ["b"] - 4
					ka ()
					-- ["c"] - 9
				-- [] - 12
			-- ["b"] - 5
			() <- jumpOut 0 $ \kb -> do
				-- [] - 6
				inFrame @"c" $ do
					-- ["c"] - 7
					kb ()
					-- ["c"] - 10
				-- [] - 11
			-- ["c"] - 8
		-- [] - 13

	do
		-- [] - 1
		inFrame @"a" $ do
			-- ["a"] - 2
			jumpOut 0 $ \k -> do
				-- [] - 3
				inFrame @"b" $ do
					-- ["b"] - 4
					k ()
			-- ["b"] - 5
			jumpOut 0 $ \k -> do

	do
		-- [] - 1
		inFrame @"a" $ do
			-- ["a"] - 2
			jumpOut 0 $ \ka -> do
				-- [] - 3
				inFrame @"b" $ do
					-- ["b"] - 4
					ka ()
					-- ["b"] - 8
			-- ["b"] - 5
			jumpOut 0 $ \kb -> do
				-- [] - 6
				inFrame @"b" $ do
					-- ["b"] - 7
					kb ()

	do
		-- [] - 1
		inFrame @"a" $ do
			-- ["a"] - 2
			jumpOut 0 $ \ka -> do
				-- [] - 3
				inFrame @"b" $ do
					-- ["b"] - 4
					ka ()
					-- ["b"] - 9
				-- [] - 12
			-- ["b"] - 5
			jumpOut 0 $ \kb -> do
				-- [] - 6
				inFrame @"b" $ do
					-- ["b"] - 7
					kb ()
					-- ["b"] - 10
				-- [] - 11
			-- ["b"] - 8
		-- [] - 13
-- -}

do
	-- [] - 1
	inFrame @"a" $ do
		-- ["a"] - 2
		inFrame @"b" $ do
			-- ["b", "a"] - 3
			jumpOut 0 $ \kb -> do
				-- ["a"] - 4
				kb ()
			-- ["a"] - 5
			jumpOut 0 $ \ka -> do
				-- [] - 6
				inFrame @"a" $ do
					-- ["a"] - 7
					inFrame @"b" $ do
						-- ["b", "a"] - 8
						ka ()
						-- ["a"] - 11
			-- ["b", "a"] - 9
		-- ["a"] - 10
