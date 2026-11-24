import YM.Eole.Expo
import YM.Eole.Part
import YM.Eole.Buds
import YM.Eole.Rate
/-! Sector exchange in the replica polynomial. Use ordered factors. -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Sample.Eole
open QCD QCD.Grass QCD.Cove Lattice Finset Ribbon Cupola Stew Function
open Lattice Wilson Creek Lat Kit NormedSpace RG Cove Filter Run
open Loom Fleet MeasureTheory Ribbon Cupola Plate Ruby
open scoped Topology BigOperators ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {I J A B:Type}[Fintype I][Fintype J][Fintype A][Fintype B]
open Quills
open Further.ShellBirth49.Fusing Collide
variable {E K:Type} {c:Side}
open Sway OrbitG Bay Strut Push.Local Push.AbsoluteSums Ursell Gas Graph Patron Kites Ribbon Cupola Plate Plate.Card Relight Ruby Massive.PCAC
namespace Gain
open QCD.GasP
local notation "m"=> Keys c 6
local notation "G"=> Grid c
local notation "P"=>Patio (m⊕Spine I)
variable {t u v x b w γ:ℝ}{U:BudgetPoint}
variable (q:I→Bool) (o:I→Site c)(F: Rail c (ample 6 I) K) (W:I→ℝ)
-- expand basis support over all physically allowed markers using F location.G
local notation "M"=> Hearts o F
set_option quotPrecheck false
local notation "V"=> withdraw 6 o t
local notation "X"=>sparkF q o F
variable (R:Reel c 6 I E)
-- root support tags proof.Y signs.
variable (Z:Bloc I J)
local notation "A"=>mark o F
local notation "Δ"=> ycard o F R
local notation "Y"=> hatsF o F
local notation "S"=>sensor q o F W R
local notation "L"=>Rootπ Z (Δ)
noncomputable def centreF : Rootπ Z (ycard o F R) ≃ K:=by
     let f (j:L):K:=j.val.fst; refine Equiv.ofBijective f ⟨?_,?_⟩
     · rintro ⟨⟨i,u⟩,hi⟩ ⟨⟨j,v⟩,hj⟩ he; change i=j at he; subst j; have hh :u=v:=Subtype.ext ((show u.val=∅ from hi).trans (show v.val=∅ from hj).symm); apply Subtype.ext; exact congr_arg (Sigma.mk i) hh
     exact fun i=> ⟨⟨⟨i,∅,mem_powerset.mpr (empty_subset _)⟩,rfl⟩,rfl⟩
variable (p:J→Site c)(k:ℕ)(Kf: E⊕Hearts o F→ℝ)
local notation "Γ"=> hood o F R k
variable (hP:Setting Z (ycard o F R) (hatsF o F) q o p (oldZ R) (hood o F R k) (sensor q o F W R t) Kf U t)
local notation "Q"=> W
local notation "hF"=> tails Z (Δ) Y q o p _ _ _ _ hP
include hP
variable (h: Wage.Tip 6 o q F U t b w) (ht:1 ≤ t)
include h ht
local notation "Φ"=>centreF o F R Z
lemma exactly (j:L) (x:Grid c) : (tails Z (Δ) Y q o p _ _ _ _ hP).warp j x = banknote 6 p t (rootR (Spine J) m ((faultK 6 o t F).warp (centreF o F R Z j) x)):=by
     let i:=ridgeQ Z (Δ) Y j; let V':=glowT Z (Δ) i.val; let P':= journal Z (Δ) q (S t) i.val; let a:= j.val; let u:= Sum.inr (α:=E) a; let z:= night (oldZ R) (S t) U.threshold x; have he:i.val={u}:=rfl; have hx: Δ u=∅:= j.property; have hpV: V'=∅:=by unfold V' glowT bins; rw[he,singleton_biUnion,hx]; rfl -- core empty defeq?
     apply congr_arg (banknote 6 p t); change Bloc.lane m q Z V' _=_; rw [hpV]; let X':=z u; have hZ:z u= (rootR (Spine I) m) ((faultK 6 o t F).warp a.fst x):=by
          have hj :mark o F a=∅:= hx; change uvBirth W (mark o F a) • sparkF q o F a x t= _; unfold sparkF; rw[hj,show uvBirth W ∅=1 from prod_empty,one_smul,Film.personality]; rfl
     change (Bloc.lane m q Z ∅) (∏ j∈i.val,z j)=_; rw [he,prod_singleton,hZ,Bloc.planted_value]; rfl
lemma spacing0 (j:L): hood o F R k (.inr j.val)=(hatsF o F j.val).place:=by let A':=j.val; unfold hood; rw [show (Δ) (.inr j.val)=_ from j.property]; unfold armsZ road; simp 
lemma mainK0 (j:L) : (tails Z (Δ) Y q o p _ _ _ _ hP).addr j=F.addr (centreF o F R Z j):=rfl
lemma root_ear : (tails Z (Δ) Y q o p _ _ _ _ hP).Reg U.threshold:=by
     let T:= (feather Z (Δ) Y q o p _ _ _ _ hP); let Vz:= stems Z (Δ) Y q o p _ _ _ _ hP; let A':=centreF o F R Z; have hp_root j:= spacing0 q o F W R Z p k Kf hP h ht j -- order
     have hw(j:L):T.addr (ridgeQ Z (Δ) Y j)=Y j.val:= (rootedT Z (Δ) Y q o p _ _ _ _ hP ht hp_root _).1; refine ⟨fun j=>?_,fun i=> Vz.measurable (ridgeQ Z (Δ) Y i),fun j=>?_,?_⟩
     · change UsesFinal _ ((Y j.val).place) (T.warp _); rw [← hw]; exact Vz.reads _
     · rw[mainK0 q o F W R Z p k Kf hP h ht]; have ht:Y j.val= F.addr (A' j):=rfl
       rw [← ht,← hw]; intro Vx; exact Vz.support _ _
     refine fun i Vx hi=> h.tilt.uses.buys (A' i) Vx fun hh=>hi ?_; rw [exactly q o F W R Z p k Kf hP h ht]; change banknote _ _ _ (rootR _ _ (vacR _ _ (withdraw _ _ _ (F.warp (A' i) Vx))))=_; rw[hh,map_zero,map_zero,map_zero,map_zero]
variable {K':Type}(Z':Rail c 6 K')
lemma poseF (hx:Correspond (faultK 6 o t F) Z') : Correspond (faultK 6 p t (tails Z (Δ) Y q o p _ _ _ _ hP)) Z':=by
     let e:= centreF o F R Z; let F0:= faultK 6 p t (tails Z (Δ) Y q o p _ _ _ _ hP); let F':= faultK 6 o t F; have hp(i:L)(U:G): F0.warp i U=F'.warp (e i) U:=by
          change vacR _ _ (withdraw _ _ _ ((tails Z (Δ) Y q o p _ _ _ _ hP).warp _ _))=_; rw [exactly q o F W R Z p k Kf hP h ht, Cupola.home 6 _ _ (zero_lt_one.trans_le ht),off]
     refine ⟨fun i=> (Summable.comp_injective (hx.pays i) e.injective).congr (fun j=> congr_arg (‖·‖) (hp j i).symm),hx.coins,fun H U=>?_⟩
     apply Eq.trans _ (hx.governs _ _); rw[fingerprint,fingerprint,← e.tsum_eq]; refine tsum_congr fun i=>?_ ; change (if F0.addr i=_ then _ else _) = _ ; have hg(i:L):F0.addr i= F'.addr (e i):=rfl; rw [hg]; split; next he=> exact hp ..
     next he=>rfl
end Gain
end YM.MassiveQCD.Sample.Eole
#print axioms YM.MassiveQCD.Sample.Eole.Gain.root_ear
#print axioms YM.MassiveQCD.Sample.Eole.Gain.poseF
