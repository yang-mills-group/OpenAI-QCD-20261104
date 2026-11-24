import YM.QCD.Garden.Trophy

/-! # consecutive prices. two levels call with categorical signs. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Garden
open Lat Kit Lattice Wilson Function Finset Filter Metric Tree RG Precision Bloch Laurent
open Orbit Birth Flume Sparks Quarry Stationary YM.Next.Free Pine Eyrie Revolve Rudder
open Extra Iteration Placement QCD.Run Work.F08 Work.F03 Exterior
open scoped Topology BigOperators Matrix Matrix.Norms.L2Operator ContDiff Classical
variable {j k m i:ℕ}{K:KernelChoices}{E:Patch}{p:Clip}{C B u v r a b c η Ω Θ:ℝ}{c₁:Side}
abbrev On := (n:Side)→Grid n→Sheet n
structure Offer (k:ℕ)(r c:ℝ) where
 roots : Type
 W : roots →Bloom k
 price : Fractal W r c
 bright : Vital (dust W)
namespace Offer
variable (U: Offer m r c)
def lamp : On:= dust U.W
def trims (ht:0≤u)(hv:u≤r)(hB:c≤B): Offer m u B:= {U with price:=reduction U.price ht hv hB}
variable {d:ℝ}
def sum (V: Offer m r a): Offer m r (c+a) where
 roots:= U.roots⊕V.roots
 W:= Sum.elim U.W V.W
 price:= Revolve.joins U.price V.price
 bright:=by
   have he : dust (Sum.elim U.W V.W) = U.lamp+V.lamp:=by ext1 i; funext j; exact gemini j U.price V.price
   rw [he]; exact U.bright.add V.bright
lemma sum_lamp (V: Offer m r a) : (U.sum V).lamp=U.lamp+V.lamp:=by ext1 i; funext j; exact gemini j U.price V.price
lemma trims_lamp (ht:0≤u)(hv:u≤r)(hB:c≤B): (U.trims ht hv hB).lamp=U.lamp:=rfl
end Offer
namespace Transfer
structure Back (E:Patch)(K:KernelChoices)(j k:ℕ)(p:Clip)(u v:ℝ) where
 path : PathData su
 fly : Flight j k
 origin : fly.patch=E
 chain : SparkMesh
 port : Place fly K chain path p u v
namespace Back
variable (A:Back E K j k p u v)
lemma has : A.fly.L=E.L:= congr_arg Patch.L A.origin
-- light at index
def charge (F:Plan j)(G:Plan k)(X:On) : A.chain.Field:=launch A.port F G X
end Back
structure Engine (A:Back E K j k p u v)(η Ω Θ:ℝ) where
 D : Bed
 D' : Bed
 T : Towers A.fly.L
 s : ℕ
 floorP (i:ℕ) : ∃ a b:ℝ, Precision.Floor D p (high A.fly A.chain i) a b
 stays (i:ℕ) : Towers.Diagonal (act A.fly K A.chain i) D D' T
 sworn (i:ℕ): Guessed (A.port.forest i) (installed (act A.fly K A.chain i).ratio T.A0) (A.port.u i)
 price : D.dual_diag.strip η Ω
 nextP : D'.diagonal.strip η Θ
 begun : 1 ≤ s
 coins : T.Deep η Ω s

variable (F:Plan j)(G:Plan k) (V:Back E K j k p u v)(J:Engine V η Ω Θ)
lemma differences (Y:On)(W:Offer m r a)(i:ℕ) : V.charge F G (Y+W.lamp) i-V.charge F G Y i = windows V.fly K (divides0 V.fly V.chain i) (Y _) F W.W (V.port.forest i) (V.port.u i):=by
  unfold Back.charge Birth.launch pulseShift; rw [Pi.sub_apply,Pi.sub_apply]; unfold windows; dsimp only [Pi.add_apply, Offer.lamp]; abel

variable (N:Push.Uniform.Before su u v E.J K i)
-- stationary multiplicativity; parameterized calls for costs
abbrev solar (T:Type*)(H:T→Back E K j k p u v)(X:T→ On): Prop:=
    ∀ Y: Quay (Orbit.Birth.stand (fun i=>(H i).chain) (fun i=>(H i).fly) K) K E p N,
      (Orbit.Birth.stand (fun i=>(H i).chain) (fun i=>(H i).fly) K).League (A:=true) (B:=true) fun j x=> X j.1 _ (Y.forge j x)
lemma solar.zips {T:Type*}(H:T→Back E K j k p u v): solar N T H (fun _=>0):= fun _=>Works.League.zeros _ true true
lemma solar.light {T:Type*}(H:T→Back E K j k p u v)(X:T→ Offer m r c)(hp:0<r): solar N T H (fun i=>(X i).lamp) := fun Y=> Y.dustborne (fun i=>(X i.1).W) hp (fun i=>(X i.1).price)
lemma solar.more {T:Type*}{H:T→Back E K j k p u v}{X Y:T→On}(h:solar N T H X)(he:solar N T H Y):solar N T H (X+Y):= fun Z=> (h Z).plus (he Z)
lemma soluble {T:Type*}(P:T→Back E K j k p u v)(X:T→On)(h:solar N T P X)(he : ∀ i,Vital (X i))(i:T) :
    Clan (P i).chain ((P i).charge F G (X i)) ∧ ∀ j,Noble ((P i).charge F G (X i) j):= qualified (S:=fun i=>(P i).chain) (fun i=>(P i).port) F G E (fun i=>(P i).origin) N he h i

lemma kind (P:Plan j)(T: Plan k) (m:ℕ)(hm:0<m)(hj:4≤j)(hk:4≤k)(hu:0<η)(hv:0≤Ω)(ht:0≤Θ): ∃ α X, 0<α∧0≤X∧∀ (K:KernelChoices)(E:Patch)(p:Clip)(u v:ℝ)
    (V: Back E K j k p u v) (J:Engine V η Ω Θ) (Y:On)(r c:ℝ)(W:Offer m r c), 0 < r → r ≤ α → (1+m) ≤E.L.val → Vital Y → (Clan V.chain (V.charge P T Y) ∧ ∀ j,Noble (V.charge P T Y j)) →(Clan V.chain (V.charge P T (Y+W.lamp)) ∧ ∀ j,Noble (V.charge P T (Y+W.lamp) j)) →
      ∃ A:Offer m r (X/(E.L.val:ℝ)^(2*m-1)*c), ∀ i,Tender ((V.charge P T (Y+W.lamp)-V.charge P T Y) i) (castF (A.lamp _)) (m+1):=by
  obtain ⟨σ,C,h,hC,H⟩:=panPrior η Ω Θ hu hj hk m hm hv ht; refine ⟨_,_,h,hC,fun K E p u v V J Y r c W hp hF hs hx ⟨hM,hW⟩ ⟨hJ,hJ'⟩=>?_⟩
  obtain ⟨⟨y,hy⟩,hz⟩:= H r c V.fly hp hF W.roots W.W J.D J.D' J.T J.s (V.has ▸ hs) J.begun J.price J.nextP J.coins W.price
  refine ⟨⟨_,_, ?_,Vital.tribute hz hp hm (fun _=>coined_port hy)⟩,fun j=>?_⟩
  · convert hz using 1; rw [V.has]
  obtain ⟨a,b,Hq⟩:= J.floorP j
  rw [Pi.sub_apply, differences ..]; have ht:0<r*(1+m):=by positivity
  apply noble_fruit J.begun hu J.nextP J.price J.coins (J.stays j) Hq hx W.bright (V.port.critical j) (J.sworn j) W.price hy hp ht ?_ ?_ hj hk
  · have h := (hJ.less hM).way j|>.ready; rwa [Pi.sub_apply, differences ..] at h
  have h: Noble (_-_) := Noble.less (hJ' j) (hW j); rwa [differences ..] at h

lemma accum (Z T B:trackG c₁)(h:Tender Z T k)(V:trackG c₁)(p:Tender B V k) : Tender (Z+B) (T+V) k:=by
  have hp:=h.2.1.sub h.2.2; have hc:=p.2.1.sub p.2.2
  refine ⟨?_,h.2.1.add p.2.1,h.2.2.add p.2.2⟩
  intro i hi; rw [show (Z+B)-(T+V)=(Z-T)+(B-V) by abel, iteratedFDeriv_add_apply (f:=Z-T) (g:=B-V) (hp.of_le le_top) (hc.of_le le_top),h.1 i hi,p.1 i hi,add_zero]
end Transfer
end YM.QCD.Garden
