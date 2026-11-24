import YM.Gust.Khaki
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Gust
open Function Set Filter Analysis Tarn Tarn.Choir QCD QCD.Lat QCD.Grass Wilson UV
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Matrix Classical
-- Kind for bosonic amplification strategy. sign on moving different kinds, diagonals ordinary.
abbrev Kind(n:ℕ):=Option (Fin n)
variable {C:Sequence}{P:Calibration C}{K:Choir}{d m n:ℕ}(T:Pollens P K) (φ:ℕ→ℕ)(G:Axle K (fun _ _=>0))(hK:K.Domestic)
namespace Kind
open Finset
abbrev q (x:Kind n) (k:Fin (n+1)):Bool:= Fin.cases x.isSome (fun i=>decide (some i=x ∧ x≠none)) k
abbrev mark (x:Kind n)(k:Fin (n+1)) :ℂ:= tauMod (q x k)
@[simp] lemma all_one(x:Kind n):∏ i:Fin (n+1),mark x i=1:=by
     rw [Fin.prod_univ_succ]; rcases x with _|x
     · simp [mark,q,tauMod]
     simp only [mark,q,Option.isSome_some,Option.some.injEq,reduceCtorEq,not_false_eq_true,and_true,Fin.cases_zero,Fin.cases_succ]; rw [prod_eq_single x]
     · simp[tauMod]
     · intro i _ h; simp[h,tauMod]
     simp
@[simp] lemma turn_m (x:Kind n)(k:Fin (n+1)):mark x k*mark x k=1:=by unfold mark; cases h:q x k<;>simp[tauMod]
end Kind
local notation "J"=>Fin (n+1)
local notation "Ix"=>Kind n
structure Mater (T:Pollens P K)(n:ℕ) where
    u:Kind n
    v:Fin (n+1)→K.W
    mem j: v j∈Col T (Kind.q u j)
abbrev Coin (x:Kind m): MultilinearMap ℂ (fun _:Fin (m+1)=>K.W) ℂ→Prop :=fun _=>True -- unused
abbrev Model (K:Choir) (n:ℕ):= Kind n→MultilinearMap ℂ (fun _:Fin (n+1)=>K.W) ℂ
abbrev Stake (T:Pollens P K)(n:ℕ):= Mater T n →₀ ℂ
namespace Mater
variable {T}
noncomputable def morph (x:Model K n) : Stake T n→ₗ[ℂ]ℂ:= Finsupp.linearCombination ℂ (fun i:Mater T n=> x i.u i.v)
noncomputable def plant (x:Mater T n):Stake T n:= Finsupp.single x 1
@[simp] lemma once(x:Mater T n)(M:Model K n):morph M (plant x)=M x.u x.v:= by simp[morph,plant]
variable (x:Mater T n)
abbrev Fees(x y:Stake T n):Prop:=∀ M:Model K n,morph M x=morph M y
variable {s:Signed}{p:EuPin}(h:p.Lifts s)
noncomputable def act (h:p.Lifts s)(x:Mater T n):Mater T n:=⟨x.u,T.spin p ∘x.v,fun i=> spinWay T hK p s h (x.mem i)⟩
noncomputable def eye (a:Axis)(x: Mater T n): Mater T n:=⟨x.u,Ch T a∘x.v,fun i=> chai T hK a _ (x.mem i)⟩
noncomputable def tint (a:Axis)(x:Mater T n):Mater T n:=⟨x.u,T.adj a ∘x.v,fun i=>litWay T hK a _ (x.mem i)⟩
variable (a:Axis)
include h
lemma coolD(x:Mater T n):x.v=(fun i=>x.v i):=rfl
lemma ajump(x:Mater T n)(i:J): T.parity ((act hK h x).v i)= Kind.mark x.u i • (act hK h x).v i:= (hue T _ _).1 ((act hK h x).mem i)
lemma slickD(q:EuPin)(hq:q.Lifts s): Fees (plant (act hK h x)) (plant (act hK hq x)) :=by
     obtain he|he:= tolerates T hK p s h q hq; all_goals intro M; rw[once,once]; change M x.u _= M x.u _
     · congr 1; change T.spin p ∘ _=T.spin q ∘ _; rw[he]
     let y:= act hK hq x; have hy:(act hK h x).v=(fun i=> Kind.mark x.u i • y.v i):=by
          funext i; change T.spin p (x.v i)=_; rw[he]; exact ((hue T _ _).1 (y.mem i))
     rw[hy,MultilinearMap.map_smul_univ,Kind.all_one,one_smul]
omit h
lemma heel: Fees (plant (eye hK a x)) (plant (eye hK timeAxis x)):=by
     intro M; simp only [once]; change M x.u (Ch _ _∘x.v)=M x.u (Ch _ _ ∘ x.v); rw [candles T hK a timeAxis]
include h
lemma eye_act: Fees (plant (eye hK a (act hK h x))) (plant (act hK h (eye hK a x))):=by
     obtain ⟨i,hi⟩:=tinted T hK a p s h; intro M; rw [once,once]; change M x.u _=M x.u _; cases i
     · congr 1; funext j; exact hi _
     let y:= act hK h (eye hK a x); have hv:(eye hK a (act hK h x)).v=fun i=> Kind.mark x.u i • y.v i:=funext fun i=> (hi _).trans ((hue T _ _).1 (y.mem i))
     rw [hv,MultilinearMap.map_smul_univ,Kind.all_one,one_smul]
omit h
lemma risen: Fees (plant (eye hK a (eye hK a x))) (plant x):=by
     obtain ⟨i,hi⟩:= blush T hK a; intro M; rw[once,once]; change M x.u _= _; cases i
     · congr 1; exact funext fun j=> hi _
     have h:(eye hK a (eye hK a x)).v=fun i=> Kind.mark x.u i • x.v i:=funext fun j=> (hi _).trans ((hue T _ _).1 (x.mem j)); rw[h,MultilinearMap.map_smul_univ,Kind.all_one,one_smul]
lemma didD: act hK (couture a) (eye hK a x)= tint hK a x:=by
     unfold act tint; congr 1; exact funext fun j=> steal T hK a _
end Mater
end YM.Massive.Gust
#print axioms YM.Massive.Gust.Mater.risen
#print axioms YM.Massive.Gust.Mater.eye_act
