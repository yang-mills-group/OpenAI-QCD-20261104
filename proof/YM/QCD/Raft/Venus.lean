import YM.QCD.Raft.Price

/-! # Actual ledger gate. Here time indexed downward from top.

Inputs to receipt on a block count chosen after width tolerance for stationary scalar gauge. Holdings post-L. Uses any gauge frames with this step and a partner-supporting *unbounded replica chain*. Tracks every contiguous interval. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Raft
open Lattice Wilson Function Finset Filter Metric RG Precision Bloch Laurent Extra Iteration QCD.Smoke
open Eyrie Stationary Quarry Work.F03 Matrix Kit Pine Orbit Birth Garden Transfer Revolve Sparks Lat
open YM.Next.Free YM.Further.PhysicalPeriodLimitF933 Jacobi Fog Voyage Flume Exterior
open scoped Topology BigOperators Matrix Matrix.Norms.L2Operator ContDiff Classical InnerProductSpace ComplexConjugate
variable {j k N:ℕ}{E:Patch}{K:KernelChoices}{p:Clip}{η Ω Θ u v t r a b c C D s G α:ℝ}
structure ParcelR where
 r :ℝ
 s :ℝ
 t :ℝ
 c :ℝ
 d :ℝ
 e :ℝ
 w :ℝ
 l :ℝ
 b :ℝ

namespace ParcelR
variable (R:ParcelR)
structure Rates (R:ParcelR)(η:ℝ):Prop where
 hr :0<R.r
 hs :0<R.s
 ht :0<R.t
 hc :0≤R.c
 hd :0≤R.d
 he :0≤R.e
 hw :0<R.w
 hl :0≤R.l
 hb :0≤R.b
 fit : R.t≤η/2
structure SunR (R:ParcelR) where
 X : Offer 1 R.r R.c
 Y : Offer 2 R.s R.d
 Z : Ornament R.t R.e
namespace SunR
variable {R}
def powerG (X:SunR R):On:= mingle X.X X.Y
lemma strong (X:SunR R): Vital X.powerG := X.X.bright.add X.Y.bright
end SunR
structure BirthR (P:Plan j)(V:Back E K j j p u v) (L: Avenue V η Ω Θ) (X Y:SunR R)(α:ℝ):Prop where
 roots (i:ℕ) : Tender (V.charge P P X.X.lamp i) (castF (Y.X.lamp _)) 2
 limbs (i:ℕ): Tender (V.charge P P X.powerG i) (castF (Y.powerG _)) 3
 bill:|α| ≤ R.b
 price:Skies P V X.powerG L.D' X.Z.page Y.Z.page α R.w R.l

def ReadyR (P:Plan j)(E:Patch)(K:KernelChoices)(p:Clip)(u v η Ω Θ:ℝ):Prop:=Rates R η ∧∀ (V:Back E K j j p u v)(L: Avenue V η Ω Θ)(X:R.SunR),∃ Y:R.SunR,∃ α:ℝ, R.BirthR P V L X Y α
lemma ranges (P:Plan j)(hj:4≤j)(he:0<η)(hΩ:0≤Ω)(hΘ:0≤Θ):∃ M:ℕ,∀ E:Patch, M≤E.L.val →∀ (K:KernelChoices)(p:Clip)(u v:ℝ)(N:ℕ)(h: Push.Uniform.Before su u v E.J K N),∃ Q:ParcelR,Q.ReadyR P E K p u v η Ω Θ:=by
  obtain ⟨t,H⟩:= harvestH P P (j:=j) hj hj he hΩ hΘ -- check signature
  obtain ⟨d,hD⟩:= Fog.crops he hΩ hΘ; refine ⟨max t d,fun E ht K p u v N b=>?_⟩
  obtain ⟨r,c,s,e,hp,hc,hP,hQ,V⟩:= H E ((le_max_left ..).trans ht) K p u v N b
  obtain ⟨x,D,A,y,Y,hx,hX,hN,hM,hL,hG,T⟩:= hD E ((le_max_right ..).trans ht) r c s e hp hc _ _ N P K u v b p -- implicit k?
  let R:ParcelR:=⟨r,s,x,c,e,D,y,Y,A⟩; refine ⟨R, ⟨hp,hc,hx,hP,hQ,hN,hL,hG,hM,hX⟩,fun B L X=>?_⟩ -- inspect order
  obtain ⟨F,U,H⟩:= V B X.X X.Y L.toEngine; obtain ⟨β,W,hβ,hB⟩:= T ⟨B,X.X,X.Y⟩ L X.Z
  exact ⟨⟨F,U,W⟩,β, fun i=>(H i).1, fun i=>(H i).2,hβ,hB⟩
end ParcelR
open ParcelR
structure Journey (E:Patch)(K:KernelChoices)(p:Clip)(u v η Ω Θ:ℝ)(j N:ℕ) where
 Periods : ℕ → ℕ→Side
 mats (i:ℕ): Train j
 station (i:ℕ)(_ : i<N): Back E K j j p u v
 engine (i:ℕ)(h:i<N): Avenue (station i h) η Ω Θ
 aligns i (h:i<N): (station i h).chain.n= Periods (i+1)
 topUp i (h:i<N) : ∀ v,localG (station i h) v=Periods i v
 inP i (h:i<N): (station i h).fly.wing=mats i
 outP i (h:i<N): (station i h).fly.land=mats (i+1)
 height (i:ℕ)(_ : i≤N): Tendsto (Periods i) atTop atTop

variable (P:Plan j) (Q: Journey E K p u v η Ω Θ j N) (R: ParcelR) {X:ℕ→ SunR R} {Y: ℕ→ℝ}
def Tally (S m:ℕ)(α:ℕ→ℝ):=∑ i∈Finset.range m,α (S+i)

def Calories (P:Plan j)(Q: Journey E K p u v η Ω Θ j N)(X:ℕ→SunR R)(A:su.Color)(i n:ℕ):ℝ := readP (rollG P (Q.mats i) (X i).powerG (Q.Periods i n)) A
omit P Q in
lemma lodging_st : ‖EuclideanSpace.single Fog.lodging (1:ℝ)‖=1:=by simp
variable (x: su.Color) (hx:‖x‖=1)(hR: Rates R η)(hv:0<η)(hp:∀ i (h:i<N),R.BirthR P (Q.station i h) (Q.engine i h) (X i) (X (i+1)) (Y i))
include hx hR hv hp
lemma embark (i l:ℕ)(h:i+l ≤ N): Tendsto (fun n=> Calories R P Q X x i n - Calories R P Q X x (i+l) n) atTop (𝓝 (Tally i l Y)):=by
  induction l with
  | zero=> simp [Tally]
  | succ l ih=>
    have hh:i+l<N:=by omega
    have H:=(hp _ hh); let V:=Q.station (i+l) hh
    have ht:= deed P P V (Q.engine (i+l) hh) x (X (i+l)).X (X (i+l)).Y (X (i+l+1)).X (X (i+l+1)).Y (X (i+l)).Z (X (i+l+1)).Z hx hR.hr hR.hc hR.hs hR.hd hR.ht hR.fit hv H.limbs hR.hw hR.hl H.price -- order of hp. deed input O
    have heq : Tendsto (fun n=> Calories R P Q X x (i+l) n-Calories R P Q X x (i+l+1) n) atTop (𝓝 (Y (i+l))):=by
      apply ht.congr'; apply Eventually.of_forall; intro n; unfold Calories; change readP (rollG P V.fly.wing (X _|>.powerG) (localG V n)) _-readP (rollG P V.fly.land (X _|>.powerG) (V.chain.n n)) _= _; unfold V; rw [Q.topUp,Q.outP,Q.aligns,Q.inP]
    rw [Tally,Finset.sum_range_succ]; refine ((ih hh.le).add heq).congr' (Eventually.of_forall fun p=> ?_)
    rw [← Nat.add_assoc]; ring
end YM.QCD.Raft
