module Types

-- attempting to prove equivalence of Types1 and Types6

import Data.Fin
import Data.Vect

data Term : Nat -> Type where
	Var : Fin n -> Term n
	Lam : Term (S n) -> Term n
	App : Term n -> Term n -> Term n
	Prompt : Term n -> Term n
	Control : Term (S n) -> Term n

	IntLit : Int -> Term n
	IntAdd : Term n -> Term n -> Term n

Trail : Type
data T1 : Type where
	Int1 : T1
	Arr1 : T1 -> Trail -> T1 -> Trail -> T1 -> T1 -> T1
Trail = List (T1, T1)
data KId : Trail -> T1 -> T1 -> Type where
	KIdNull : {a : T1} -> KId [] a a
	KIdSing : {tau1, tau2 : T1} -> KId [(tau1, tau2)] tau1 tau2
data Cons : Trail -> Trail -> Trail -> Type where
	ConsRNull : {mu : Trail } -> Cons mu [] mu
	ConsLNull : {mu : Trail } -> Cons [] mu mu
	ConsCons : {a, r, tau1, tau2 : T1} -> {mu1, mu2, mu3 : Trail} ->
		Cons ((tau1, tau2)::mu2) mu3 mu1 ->
		Cons ((a, r)::mu1) ((tau1, tau2)::mu2) ((a, r)::mu3)
data Typed1 : Term n -> Vect n T1 -> Trail -> T1 -> Trail -> T1 -> T1 -> Type where
	Var1 : {delta : T1} -> {mu : Trail} ->
		(i : Fin n) -> Typed1 (Var i) vars mu delta mu delta (index i vars)
	Lam1 : {e : Term (S n)} -> {a, b, beta, alpha, delta : T1} -> {mu_beta, mu_alpha, mu : Trail} ->
		Typed1 e (a :: vars) mu_beta beta mu_alpha alpha b ->
		Typed1 (Lam e) vars mu delta mu delta (Arr1 a mu_beta beta mu_alpha alpha b)
	App1 : {f, a : Term n} -> {ta, tb, alpha1, alpha2, alpha3, alpha4 : T1} -> {mu1, mu2, mu3, mu4 : Trail} ->
		Typed1 f vars mu1 alpha1 mu2 alpha2 (Arr1 ta mu3 alpha3 mu4 alpha4 tb) ->
		Typed1 a vars mu2 alpha2 mu3 alpha3 ta ->
		Typed1 (App f a) vars mu1 alpha1 mu4 alpha4 tb
	Prompt1 : {e : Term n} -> {mu_id, mu_alpha : Trail} -> {beta', beta, alpha, tau : T1} ->
		KId mu_id beta beta' ->
		Typed1 e vars [] tau mu_id beta' beta ->
		Typed1 (Prompt e) vars mu_alpha alpha mu_alpha alpha tau
	Control1 : {e : Term (S n)} -> {mu_id, mu0, mu1, mu2, mu_beta, mu_alpha : Trail} -> {γ, γ', tau1, tau2, beta, alpha, tau : T1} ->
		KId mu_id γ γ' ->
		Cons ((tau1, tau2)::mu1) mu2 mu0 ->
		Cons mu_beta mu0 mu_alpha ->
		Typed1 e (Arr1 tau mu2 alpha mu1 tau2 tau1 :: vars) [] beta mu_id γ' γ ->
		Typed1 (Control e) vars mu_beta beta mu_alpha alpha tau

	IntLit1 : {mu_alpha : Trail} -> {alpha : T1} ->
		(v : Int) -> Typed1 (IntLit v) vars mu_alpha alpha mu_alpha alpha Int1
	IntAdd1 : {l, r : Term n} -> {beta, delta, alpha : T1} -> {mu_beta, mu_delta, mu_alpha : Trail} ->
		Typed1 l vars mu_beta beta mu_delta delta Int1 ->
		Typed1 r vars mu_delta delta mu_alpha alpha Int1 ->
		Typed1 (IntAdd l r) vars mu_beta beta mu_alpha alpha Int1

data Strat : Type where
	Stop : Strat
	PropShift : Strat
mutual
	data T6 : Type where
		Int6 : T6
		Arr6 : T6 -> Context -> Context -> T6 -> T6
	data Context : Type where
		H : Strat -> Context -> Context -> T6 -> Context
data InterpH : Strat -> T6 -> Context -> Context -> T6 -> Type where
	InterpHStop : {a, r, tau : T6} -> {delta, beta, alpha, sigma : Context} ->
		InterpH Stop
			(Arr6
				(Arr6 a delta delta a)
				(H Stop beta alpha r)
				(H strat sigma sigma tau)
				tau)
			beta alpha r
	InterpHPropShift :
		{delta, beta, alpha, f_beta, f_alpha, beta', alpha' : Context} ->
		{tau2, a, f_tau, tau3, tau : T6} ->
		InterpH strat
			(Arr6
				(Arr6 tau2 delta alpha a)
				f_beta f_alpha f_tau)
			beta' alpha' tau3 ->
		InterpH PropShift
			(Arr6
				(Arr6 tau beta alpha a)
				f_beta f_alpha f_tau)
			(H strat beta' alpha' tau3)
			(H PropShift beta delta tau2)
			tau
data Typed6 : Term n -> Vect n T6 -> Context -> Context -> T6 -> Type where
	Var6 : {delta : Context} ->
		(i : Fin n) -> Typed6 (Var i) vars delta delta (index i vars)
	Lam6 : {e : Term (S n)} -> {a, b : T6} -> {beta, alpha, delta : Context} ->
		Typed6 e (a :: vars) beta alpha b ->
		Typed6 (Lam e) vars delta delta (Arr6 a beta alpha b)
	App6 : {f, a : Term n} -> {ta, tb : T6} -> {alpha1, alpha2, alpha3, alpha6 : Context} ->
		Typed6 f vars alpha1 alpha2 (Arr6 ta alpha3 alpha6 tb) ->
		Typed6 a vars alpha2 alpha3 ta ->
		Typed6 (App f a) vars alpha1 alpha6 tb
	Prompt6 : {alpha, delta : Context} -> {r, tau : T6} ->
		Typed6 e vars (H Stop alpha alpha r) (H strat_alpha delta delta tau) tau ->
		Typed6 (Prompt e) vars alpha alpha r
	C6 :
		{delta, beta, alpha, f_beta, f_alpha, beta', alpha' : Context} ->
		{b, a, f_tau, tau', tau : T6} ->
		InterpH strat_beta (Arr6 (Arr6 b delta alpha a) f_beta f_alpha f_tau) beta' alpha' tau' ->
		Typed6 e (Arr6 tau beta alpha a :: vars) f_beta f_alpha f_tau ->
		Typed6 (Control e) vars (H strat_beta beta' alpha' tau') (H PropShift beta delta b) tau

	IntLit6 : {alpha : Context} ->
		(v : Int) -> Typed6 (IntLit v) vars alpha alpha Int6
	IntAdd6 : {l, r : Term n} -> {beta, delta, alpha : Context} ->
		Typed6 l vars beta delta Int6 ->
		Typed6 r vars delta alpha Int6 ->
		Typed6 (IntAdd l r) vars beta alpha Int6

vectIndexMap : (i : Fin n) -> (f : a -> b) -> (v : Vect n a) -> index i (map f v) = f (index i v)

mutual
	conv16Context : Context -> Trail -> T1 -> Context
	conv16Type : Context -> T1 -> T6

	conv16Type ctx Int1 = Int6
	conv16Type ctx (Arr1 a mu_beta beta mu_alpha alpha b) = Arr6
		(conv16Type ctx a)
		(conv16Context ctx mu_beta beta)
		(conv16Context ctx mu_alpha alpha)
		(conv16Type ctx b)

	conv16Context ctx [] t = H Stop ctx ctx (conv16Type ctx t)
	conv16Context ctx ((a, b) :: mu) t = H PropShift
		(H Stop ctx ctx (conv16Type ctx b))
		(conv16Context ctx mu t)
		(conv16Type ctx a)
conv16T :
	{n : Nat} ->
	{t : Term n} ->
	{vars : Vect n T1} ->
	{mu_beta, mu_alpha : Trail} ->
	{beta, alpha, tau : T1} ->
	(ctx : Context) ->
	Typed1 t vars mu_beta beta mu_alpha alpha tau ->
	Typed6 t
		(map (Types.conv16Type ctx) vars)
		(Types.conv16Context ctx mu_beta beta)
		(Types.conv16Context ctx mu_alpha alpha)
		(Types.conv16Type ctx tau)
conv16T ctx (Var1 i) = replace
	{p = \inner =>
		Typed6 t
			(map (conv16Type ctx) vars)
			(conv16Context ctx mu_beta beta)
			(conv16Context ctx mu_alpha alpha)
			inner}
	(vectIndexMap i (conv16Type ctx) vars)
	(Var6 i)
conv16T ctx (Lam1 te) = Lam6 (conv16T ctx te)
conv16T ctx (App1 tf ta) = App6 (conv16T ctx tf) (conv16T ctx ta)
conv16T ctx (Prompt1 KIdNull te) = ?t_6
conv16T ctx (Prompt1 KIdSing te) = Prompt6 (conv16T ctx te)
conv16T ctx (Control1 kid cons1 cons2 te) = ?t_5
conv16T ctx (IntLit1 v) = IntLit6 v
conv16T ctx (IntAdd1 tl tr) = IntAdd6 (conv16T ctx tl) (conv16T ctx tr)
