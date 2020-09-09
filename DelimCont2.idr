data HasPrompt : Type -> List Type -> Type where
	-- t is the type the prompt returns
	Head : HasPrompt t (t :: ts)
	Tail : HasPrompt t ts -> HasPrompt t (t'1 :: t'2 :: ts)
hpPostTs : HasPrompt t ts -> List Type
hpPostTs (Head {ts}) = ts
hpPostTs (Tail hp) = hpPostTs hp

not_not_id : (a : Bool) -> a = not (not a)
not_not_id False = Refl
not_not_id True = Refl

{-
namespace fn
	mutual
		Op : (Type -> Type) -> Type -> List Type -> Type
		Op m r ts = Conts m r ts -> m r

		data Conts : (Type -> Type) -> Type -> List Type -> Type where
			Nil : Conts m r []
			(::) : (t -> Op m r ts) -> Conts m r ts -> Conts m r (t :: ts)

	hpK : (hp : HasPrompt t ts) -> Conts m r ts -> t -> Op m r (hpPostTs hp)
	hpK Head (k :: ks) = k
	hpK (Tail hp) (_ :: _ :: ks) = hpK hp ks
	hpPostKs : (hp : HasPrompt t ts) -> Conts m r ts -> Conts m r (hpPostTs hp)
	hpPostKs Head (_ :: ks) = ks
	hpPostKs (Tail hp) (_ :: _ :: ks) = hpPostKs hp ks
	hpReplaceNonPreKs : (hp : HasPrompt t ts) -> Conts m r ts -> Conts m r (t :: hpPostTs hp) -> Conts m r ts
	hpReplaceNonPreKs Head _ ks' = ks'
	hpReplaceNonPreKs (Tail hp) (k1 :: k2 :: ks) ks' = k1 :: k2 :: hpReplaceNonPreKs hp ks ks'

	map : (a -> b) -> Op m r (a :: ts) -> Op m r (b :: ts)
	map f a = \(k :: ks) => a $ k . f :: ks

	pure : a -> Op m r (a :: ts)
	pure a = \(k :: ks) => k a ks

	join : Op  m r(Op m r (a :: ts) :: ts) -> Op m r (a :: ts)
	join a = \(k :: ks) => a $ (:: ks) $ \a => \ks => a $ k :: ks

	liftM : Monad m => m a -> Op m r (a :: ts)
	liftM m = \(k :: ks) => m >>= \x => k x ks

	liftP : Op m r (a :: ts) -> Op m r (a :: b :: c :: ts)
	liftP m = \(ka :: kb :: kc :: ks) => m $ (\a => \ks' => ka a (kb :: kc :: ks')) :: ks

	prompt0' : Op m r (n :: n :: j :: ts) -> Op m r (Either j n :: ts)
	prompt0' e = \(ka :: ks) => e $
		(\n => \(kn :: ks) => kn n ks) ::
		(\n => \(_ :: ks) => ka (Right n) ks) ::
		(\j => \ks => ka (Left j) ks) ::
		ks

	prompt0 : Op m r (a :: a :: a :: ts) -> Op m r (a :: ts)
	-- prompt0 e = \ks => e $ pure :: pure :: ks
	prompt0 e = map fromEither $ prompt0' e
	-- prompt0 e = \ks => e $ pure :: (\n => \(_ :: ks) => ka n ks) :: ks

	control0 :
		(hp : HasPrompt t ts) ->
		(
			(a -> Op m r (t :: t' :: hpPostTs hp)) -> 
			Op m r (hpPostTs hp)
		) ->
		Op m r (a :: ts)
	control0 hp f = \(ka :: ks) => f
		(\x => \(k' :: kr :: ks') =>
			ka x $ hpReplaceNonPreKs hp ks $
			(\x' => \ks'' => k' x' (kr :: ks'')) :: ks'
		)
		(hpPostKs hp ks)

	(>>=) : Op m r (a :: ts) -> (a -> Op m r (b :: ts)) -> Op m r (b :: ts)
	a >>= f = join $ map f a
	-- a >>= f = \(k :: ks) => a $ (:: ks) $ \a => \ks => f a $ k :: ks

	{-
	\(k :: ks) => flip prompt0' (k . fromEither :: ks) $ control0 Head f >>= c
	\(k :: ks) => flip prompt0' (k . fromEither :: ks) $ join $ map c $ control0 Head f
	\(k :: ks) => flip join (
		(\n, (kn :: ks) => kn n ks) ::
		(\n, (_ :: ks) => k n ks) ::
		(\j, ks => k j ks) ::
	ks) $ map c $ control0 Head f
	\(k :: ks) => flip (map c) (
		(\a, ks => a $ (\n, (kn :: ks) => kn n ks) :: ks) ::
		(\n, (_ :: ks) => k n ks) ::
		(\j, ks => k j ks) ::
	ks) $ control0 Head f
	\(k :: ks) => control0 Head f (
		(\a, ks => c a $ (\n, (kn :: ks) => kn n ks) :: ks) ::
		(\n, (_ :: ks) => k n ks) ::
		(\j, ks => k j ks) ::
	ks)
	\(k :: ks) => f
		(\x, (k' :: kr :: ks') =>
			(\ks => c x $ (\n, (kn :: ks) => kn n ks) :: ks) $
			(\x', ks'' => k' x' (kr :: ks'')) :: ks'
		)
		((\j, ks => k j ks) :: ks)
	\(k :: ks) => f
		(\x, (k' :: kr :: ks') => c x $
			(\n, (kn :: ks) => kn n ks) ::
			(\x', ks'' => k' x' (kr :: ks'')) ::
		ks')
		(k :: ks)
	-}

	(<*>) : Op m r ((a -> b) :: ts) -> Op m r (a :: ts) -> Op m r (b :: ts)
	-- f <*> a = \(k :: ks) => f $ (:: ks) $ \f => \ks => a $ (:: ks) $ \a => \ks => k (f a) ks
	f <*> a = f >>= \f => map f a

	rebase :
		(hp : HasPrompt b ts) ->
		Conts m r (a :: ts) ->
		a -> Op m r (b :: t :: hpPostTs hp)
	-- rebase hp (ka :: ks) a (kb :: kt :: ks') = ka a $ hpReplaceNonPreKs hp ks $ (\b, ks'' => kb b (kt :: ks'')) :: ks'
	rebase Head (ka :: _) a (kb :: kt :: ks) = ka a $ (\b, ks' => kb b (kt :: ks')) :: ks
	-- rebase Head ks a ks' = control0 Head (\f, _ => f a ks') ks
	rebase (Tail hp) (ka :: k1 :: k2 :: ks) a ks' = rebase hp ((\a, ks'' => ka a (k1 :: k2 :: ks'')) :: ks) a ks'
	-- rebase (Tail hp) ks a ks' = flip liftP ks $ \ks => rebase hp ks a ks'
	replacePrompt : (hp : HasPrompt t ts) -> Op m r (hpPostTs hp) -> Op m r (a :: ts)
	replacePrompt Head m = control0 {t' = ()} Head (\_, ks' => m ks')
	-- replacePrompt Head m = \(_ :: _ :: ks) => m ks
	replacePrompt (Tail hp) m = liftP $ \ks => replacePrompt hp m ks

	control0' :
		(hp : HasPrompt t ts) ->
		(
			(a -> Op m r (t :: t' :: hpPostTs hp)) -> 
			Op m r (hpPostTs hp)
		) ->
		Op m r (a :: ts)
	control0' hp f ks = replacePrompt hp (f $ rebase hp ks) ks
-- -}

{-
namespace free
	data Instr : (List Type -> Type) -> (Type -> Type) -> Type -> Type where
		Bind : (ks (a :: ts) -> Instr ks m r) -> (a -> ks (b :: ts) -> Instr ks m r) -> ks (b :: ts) -> Instr ks m r
		LiftM : m a -> ks (a :: ts) -> Instr ks m r
		LiftP : (ks (a :: ts) -> Instr ks m r) -> ks (a :: b :: c :: ts) -> Instr ks m r
		RebaseHead : ks (a :: b :: ts) -> a -> ks (b :: t :: ts) -> Instr ks m r
		ReplacePromptHead : (ks ts -> Instr ks m r) -> ks (a :: b :: ts) -> Instr ks m r
		Prompt : (ks (n :: n :: j :: ts) -> Instr ks m r) -> ks (Either j n :: ts) -> Instr ks m r
		Done : r -> Instr ks m r

	data Conts' : (Type -> Type) -> Type -> List Type -> Type where
		Nil : Conts' m r ts
		(::) : (t -> Conts' m r ts -> Instr (Conts' m r) m r) -> Conts' m r ts -> Conts' m r (t :: ts)

	runInstr : Monad m => ({ks : List Type -> Type} -> {r : Type} -> ks ts -> Instr ks m r) -> Conts' m r ts -> m r
	runInstr {m} {r} e ks = go $ e ks
		where
			go : Instr (Conts' m r) m r -> m r
			go (Bind ea f (k :: ks)) = go $ ea $ (:: ks) $ \a, ks => f a $ k :: ks
			go (LiftM ma (k :: ks)) = ma >>= \a => go $ k a ks
			go (LiftP ea (ka :: kb :: kc :: ks)) = go $ ea $ (:: ks) $ \a, ks => ka a $ kb :: kc :: ks
			go (RebaseHead (ka :: _) a (kb :: kt :: ks)) = go $ ka a $ (:: ks) $ \b, ks => kb b $ kt :: ks
			go (ReplacePromptHead e (_ :: _ :: ks)) = go $ e ks
			go (Prompt e (k :: ks)) = go $ e $
				(LiftM . pure) ::
				(\n, (_ :: ks) => k (Right n) ks) ::
				(\j, ks => k (Left j) ks) ::
				ks
			go (Done r) = pure r

	pure : Applicative m => a -> ks (a :: ts) -> Instr ks m r
	pure = LiftM . pure

	map : Applicative m => (a -> b) -> (ks (a :: ts) -> Instr ks m r) -> ks (b :: ts) -> Instr ks m r
	map f a = Bind a (free.pure . f)

	join : (ks ((ks (a :: ts) -> Instr ks m r) :: ts) -> Instr ks m r) -> ks (a :: ts) -> Instr ks m r
	join a = Bind a id

	rebase :
		(hp : HasPrompt b ts) ->
		ks (a :: ts) -> a ->
		ks (b :: t :: hpPostTs hp) ->
		Instr ks m r
	rebase Head = RebaseHead
	rebase (Tail hp) = \ks, a, ks' => flip LiftP ks $ \ks => rebase hp ks a ks'

	replacePrompt : (hp : HasPrompt t ts) -> (ks (hpPostTs hp) -> Instr ks m r) -> ks (a :: ts) -> Instr ks m r
	replacePrompt Head = ReplacePromptHead
	replacePrompt (Tail hp) = \m => LiftP $ \ks => replacePrompt hp m ks

	control0 :
		{t : Type} ->
		(hp : HasPrompt t ts) ->
		(
			(a -> ks (t :: t' :: hpPostTs hp) -> Instr ks m r) -> 
			ks (hpPostTs hp) -> Instr ks m r
		) ->
		ks (a :: ts) -> Instr ks m r
	control0 hp f ks = replacePrompt hp (f $ rebase hp ks) ks
-}

namespace free2
	data Ref : List (Bool, List Type) -> (Bool, List Type) -> Type where
		Head : Ref (ts :: tss) ts
		Tail : Ref tss ts -> Ref (ts' :: tss) ts
	rPostTss : Ref tss ts -> List (Bool, List Type)
	rPostTss (Head {tss}) = tss
	rPostTss (Tail r) = rPostTss r
	data Instr : List (Bool, List Type) -> (Type -> Type) -> Type -> Type where
		Prim1 : Instr ((True, a :: ts) :: tss) m r -> (a -> Instr ((False, ts) :: tss) m r) -> Ref tss (False, ts) -> Instr tss m r
		Prim2 : Instr ((not u, ts) :: tss) m r -> Ref tss (u, t :: ts) -> Instr tss m r
		Bind : Instr ((True, a :: ts) :: tss) m r -> (a -> Instr ((True, b :: ts) :: tss) m r) -> Ref tss (True, b :: ts) -> Instr tss m r
		LiftM : m a -> Ref tss (True, a :: ts) -> Instr tss m r
		LiftP : Instr ((True, a :: ts) :: tss) m r -> Ref tss (True, a :: b :: c :: ts) -> Instr tss m r
		RebaseHead : Ref tss (True, a :: b :: ts) -> a -> Ref tss (True, b :: t :: ts) -> Instr tss m r
		ReplacePromptHead : Instr ((True, ts) :: tss) m r -> Ref tss (True, a :: b :: ts) -> Instr tss m r
		Prompt : Instr ((True, n :: n :: j :: ts) :: tss) m r -> Ref tss (True, Either j n :: ts) -> Instr tss m r
		Done : r -> free2.Instr tss m r

	namespace Conts
		data Conts : List (Bool, List Type) -> (Type -> Type) -> Type -> (Bool, List Type) -> Type where
			Nil : Conts tss m r (False, ts)
			(::) : (t -> Instr ((not u, ts) :: tss) m r) -> Conts tss m r (not u, ts) -> Conts tss m r (u, t :: ts)
		uncons : Conts tss m r (u, t :: ts) -> (t -> Instr ((not u, ts) :: tss) m r, Conts tss m r (not u, ts))
		uncons (k :: ks) = (k, ks)

	namespace Contss
		data Contss : List (Bool, List Type) -> (Type -> Type) -> Type -> Type where
			Nil : Contss [] m r
			(::) : Conts tss m r ts -> Contss tss m r -> Contss (ts :: tss) m r
		index : (ref : Ref tss ts) -> Contss tss m r -> (Conts (rPostTss ref) m r ts, Contss (rPostTss ref) m r)
		index Head (ks :: kss) = (ks, kss)
		index (Tail ref) (_ :: kss) = index ref kss

	runInstr : Monad m => ({r : Type} -> Instr tss m r) -> Contss tss m r -> m r
	runInstr {m} {r} e kss = go e kss
		where
			go : Instr tss m r -> Contss tss m r -> m r
			go (Done r) kss = pure r

	bind : Instr ((True, a :: ts) :: tss) m r -> (a -> Instr ((True, b :: ts) :: tss) m r) -> Ref tss (True, b :: ts) -> Instr tss m r
	bind ea faeb rks = flip Prim2 rks $ flip (Prim1 (?t ea)) Head $ \a => ?t

	-- TODO
	-- liftP : Instr ((True, a :: ts) :: tss) m r -> Ref tss (True, a :: b :: c :: ts) -> Instr tss m r
	-- liftP e rks = Prim2 (Prim2 (?t e) Head) rks

	pure : Applicative m => a -> Ref kss (True, a :: ts) -> Instr kss m r
	pure = LiftM . pure

	map : Applicative m => (a -> b) -> Instr ((True, a :: ts) :: kss) m r -> Ref kss (True, b :: ts) -> Instr kss m r
	map f a = Bind a $ \a => pure (f a) Head

	join : Instr ((True, Instr ((True, a :: ts) :: kss) m r :: ts) :: kss) m r -> Ref kss (True, a :: ts) -> Instr kss m r
	join a = Bind a id

	rebase :
		(hp : HasPrompt b ts) ->
		Ref kss (True, a :: ts) -> a ->
		Ref kss (True, b :: t :: hpPostTs hp) ->
		Instr kss m r
	rebase Head = RebaseHead
	rebase (Tail hp) = \ks, a, ks' => LiftP (rebase hp Head a (Tail ks')) ks

	replacePrompt : (hp : HasPrompt t ts) -> Instr ((True, hpPostTs hp) :: kss) m r -> Ref kss (True, a :: ts) -> Instr kss m r
	replacePrompt Head = ReplacePromptHead
	replacePrompt (Tail hp) = \m => LiftP $ replacePrompt hp ?t Head

	control0 :
		{t : Type} ->
		(hp : HasPrompt t ts) ->
		(
			(a -> Instr ((True, t :: t' :: hpPostTs hp) :: kss) m r) -> 
			Instr ((True, hpPostTs hp) :: kss) m r
		) ->
		Ref kss (True, a :: ts) -> Instr kss m r
	control0 hp f ks = replacePrompt hp (f $ \a => rebase hp (Tail ks) a Head) ks

data Inspect : a -> Type where
	MkInspect : Inspect a
