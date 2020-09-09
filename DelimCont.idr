import Control.Monad.Identity

{-
map f a = \(k :: ks) => a $ k . f :: ks
pure a = \(k :: ks) => k a ks
f <*> a = \(k :: ks) => f $ (:: ks) $ \f => \ks => a $ k . f :: ks
a >>= f => \(k :: ks) => a $ (:: ks) $ \a => \ks => f a $ k :: ks
lift m = \(k :: ks) => m >>= \x => k x ks
prompt0 e = \ks => e $
	(\x => \(k :: ks) => k x ks) ::
	(\x => \(k :: ks) => k x ks) ::
	ks
control0 hp f = \(ka :: ks) => f
	(\x => \(k' :: kr :: ks') => ka x $ hpReplaceNonPreKs hp ks $ (\x' => \ks'' => k' x' (kr :: ks'')) :: ks')
	(snd (hpK hp ks) :: hpPostKs hp ks)

prompt0
	\ks => pure :: pure :: ks
control0 hp
	\ks => \(k' :: kr :: ks') => hpPreKs hp ks ++ (\x' => \ks'' => k' x' (kr :: ks'')) :: ks'
	\(ka :: ks) => snd (hpK hp ks) :: hpPostKs hp ks
-}

data Conts : List Type -> (Type -> Type) -> Type -> Type where
	Nil : Conts [] m r
	(::) : (t -> Conts ts m r -> m r) -> Conts ts m r -> Conts (t :: ts) m r

promptContTs : List (String, Type) -> List Type
promptContTs [] = []
promptContTs ((tag, t) :: ps) = t :: t :: promptContTs ps

data HasPrompt : String -> Type -> List (String, Type) -> Type where
	Head : HasPrompt tag t ((tag, t) :: ps)
	Tail : Not (tag' = tag) -> HasPrompt tag t ps -> HasPrompt tag t ((tag', t') :: ps)
hpPrePs : HasPrompt tag t ps -> List (String, Type)
hpPrePs Head = []
hpPrePs (Tail {tag'} {t'} _ t) = (tag', t') :: hpPrePs t
hpPostPs : HasPrompt tag t ps -> List (String, Type)
hpPostPs (Head {ps}) = ps
hpPostPs (Tail _ t) = hpPostPs t
hpK :
	(hp : HasPrompt tag t ps) ->
	Conts (promptContTs ps) m r ->
	(
		t -> Conts (t :: promptContTs (hpPostPs hp)) m r -> m r,
		t -> Conts (promptContTs (hpPostPs hp)) m r -> m r
	)
hpK Head (kr :: kj :: ks) = (kr, kj)
hpK (Tail _ hp) (kr' :: kj' :: ks) = hpK hp ks
hpPostKs :
	(hp : HasPrompt tag t ps) ->
	Conts (promptContTs ps) m r ->
	Conts (promptContTs $ hpPostPs hp) m r
hpPostKs Head (kr :: kj :: ks) = ks
hpPostKs (Tail _ hp) (kr' :: kj' :: ks) = hpPostKs hp ks
hpReplaceK :
	(hp : HasPrompt tag t ps) ->
	Conts (promptContTs ps) m r ->
	(
		t -> Conts (t :: promptContTs (hpPostPs hp)) m r -> m r,
		t -> Conts (promptContTs (hpPostPs hp)) m r -> m r
	) ->
	Conts (promptContTs ps) m r
hpReplaceK Head (_ :: _ :: ks) (kr, kj) = kr :: kj :: ks
hpReplaceK (Tail _ hp) (kr' :: kj' :: ks) (kr, kj) = kr' :: kj' :: hpReplaceK hp ks (kr, kj)
hpReplacePostKs :
	(hp : HasPrompt tag t ps) ->
	Conts (promptContTs ps) m r ->
	Conts (promptContTs $ hpPostPs hp) m r ->
	Conts (promptContTs ps) m r
hpReplacePostKs Head (kr :: kj :: ks) ks' = kr :: kj :: ks'
hpReplacePostKs (Tail _ hp) (kr' :: kj' :: ks) ks' = kr' :: kj' :: hpReplacePostKs hp ks ks'

record Cont (r : Type) (ps : List (String, Type)) (m : Type -> Type) (a : Type) where
	constructor MkCont
	runCont : Conts (a :: promptContTs ps) m r -> m r

Functor (Cont r ps m) where
	map f a = assert_total $ MkCont $ \(k :: ks) => runCont a $ k . f :: ks
Applicative (Cont r ps m) where
	pure a = assert_total $ MkCont $ \(k :: ks) => k a ks
	f <*> a = assert_total $ MkCont $ \(k :: ks) => runCont f $ (:: ks) $ \f, ks => runCont a $ k . f :: ks
Monad (Cont r ps m) where
	a >>= f = assert_total $ MkCont $ \(k :: ks) => runCont a $ (:: ks) $ \a, ks' => runCont (f a) $ k :: ks'

lift : Monad m => m a -> Cont r ps m a
lift m = MkCont $ \(k :: ks) => m >>= flip k ks

-- TODO: I think these are prompt0/control0?

prompt0 : (tag : String) -> Cont r ((tag, t) :: ps) m t -> Cont r ps m t
prompt0 {r} {m} {t} {ps} tag e = MkCont $ \(kj :: ks) => runCont e $
	(\x, (k :: ks') => k x ks') :: -- k', gets merged with other things
	(\x, (k :: ks') => k x ks') :: -- kr, replace to handle return
	kj :: -- kj, replace to handle jumps
	ks

control0 : (tag : String) -> {auto hp : HasPrompt tag t ps} ->
	((a -> Cont r ((tag, t) :: hpPostPs hp) m t) -> Cont r (hpPostPs hp) m t) -> Cont r ps m a
control0 {a} {ps} {hp} {t} tag f = MkCont $ \(ka :: ks) => runCont
		(f $ MkCont . go_c (ka :: ks))
		(snd (hpK hp ks) :: hpPostKs hp ks)
	where
		go_c :
			Conts (a :: promptContTs ps) m r ->
			a ->
			Conts (t :: t :: t :: promptContTs (hpPostPs hp)) m r ->
			m r
		go_c (ka :: ks) x (k' :: kr :: kj :: ks') =
			ka x $ hpReplaceK hp (hpReplacePostKs hp ks ks') (\x', ks'' => k' x' (kr :: ks''), kj)

{-
prf :
	(ps : List (String, Type)) ->
	(ks : Conts r (a :: promptContTs ps) m) ->
	(c : a -> Cont r ((tag, a) :: ps) m a) ->
	(f : (a -> Cont r ((tag, a) :: ps) m a) -> Cont r ps m a) ->
	runCont (prompt0 tag (control0 tag f >>= c)) ks = runCont (f c) ks
prf ps (ka :: ks) c f = ?t_1

id_k x (k :: ks) = k x ks
bind_k f k a ks' = runCont (f a) (k :: ks')
control_k (ka :: ks) x (k' :: kr :: kj :: ks') = ka x $ hpReplaceK hp (hpReplacePostKs hp ks ks') (\x', ks'' => k' x' (kr :: ks''), kj)

runCont (prompt0 {m = Identity} tag (control0 tag f >>= c)) (ka :: ks)
runCont (control0 tag f >>= c) (id_k :: id_k :: ka :: ks)
runCont (control0 tag f) (bind_k c id_k :: id_k :: ka :: ks)
runCont (f $ MkCont . control0.go_c (bind_k c id_k :: id_k :: ka :: ks)) (ka :: ks)
runCont (f $ \x => MkCont $ \(k' :: kr :: kj :: ks') => bind_k c id_k x $ hpReplaceK hp (hpReplacePostKs hp (id_k :: ka :: ks) ks') (\x', ks'' => k' x' (kr :: ks''), kj)) (ka :: ks)
runCont (f $ \x => MkCont $ \(k' :: kr :: kj :: ks') => bind_k c id_k x $ hpReplaceK hp (id_k :: ka :: ks') (\x', ks'' => k' x' (kr :: ks''), kj)) (ka :: ks)
runCont (f $ \x => MkCont $ \(k' :: kr :: kj :: ks') => bind_k c id_k x $ (\x', ks'' => k' x' (kr :: ks'')) :: kj :: ks') (ka :: ks)
runCont (f $ \x => MkCont $ \(k' :: kr :: kj :: ks') => runCont (c x) $ id_k :: (\x', ks'' => k' x' (kr :: ks'')) :: kj :: ks') (ka :: ks)
runCont (f $ \x => MkCont $ \(k' :: kr :: ks) => runCont (c x) $ id_k :: (\x', ks'' => k' x' (kr :: ks'')) :: ks) (ka :: ks)
-}
