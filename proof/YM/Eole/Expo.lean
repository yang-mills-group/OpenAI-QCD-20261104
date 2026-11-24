import YM.Eole.Stars
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
abbrev oldZ (i:E):= (R.addr i).support
abbrev kiteA (L:Finset I) := uvBirth W L
noncomputable def piece (i:E) : Grid c→ Patio ((Keys c 6)⊕ Spine I):= uvBirth W (R.z i) • R.mark i
variable (A':Bloc I J)(p:J→Site c)(k:ℕ)
local notation "O"=> E⊕ Hearts o F
noncomputable abbrev adress : E⊕Hearts o F→ Hat c := Sum.elim (fun i:E=>⟨ oldZ R i,(R.addr i).support, ⟨_, (R.addr i).anchor⟩,Subset.rfl⟩) (hatsF o F) -- dummy
noncomputable def road : E⊕Hearts o F→ Support c:=Sum.elim (oldZ R) (fun i=> (hatsF o F i).place)
noncomputable def ycard : E ⊕ Hearts o F→ Finset I:= Sum.elim R.z (mark o F) -- W Binder mark Root. 
noncomputable abbrev hood (k:ℕ) (i:E⊕Hearts o F) := armsZ o k (road o F R i) (ycard o F R i)
noncomputable def sensor (t:ℝ) : E ⊕ Hearts o F→ Grid c → Patio ((Keys c 6)⊕Spine I):= Sum.elim (piece W R) (fun i=> fullK q o F W i t)
noncomputable abbrev pointZ (t:ℝ)(s:Finset I)(p:ℝ):= t^s.card*p
noncomputable def spareK (V1:E→ℝ)(V2:K→ℝ)(t:ℝ) : E⊕Hearts o F →ℝ :=fun i=>pointZ t (ycard o F R i) (Sum.elim V1 (V2∘Sigma.fst) i)
lemma levelFunds (w:ℝ)(hw:∀ i,|W i|≤w)(s:Finset I) : ‖uvBirth W s‖ ≤ w^s.card:=by
    unfold uvBirth; rw [norm_prod,←Finset.prod_const]; apply prod_le_prod (fun i _=> norm_nonneg _); intro i _; exact (Complex.norm_real _).trans_le (hw _)
lemma windV {P':Support c}{Y:Grid c→Alg m}{i:Site c}(hp:Sight P' i k U t Y u)(z:ℂ): Sight P' i k U t (z • Y) (‖z‖*u):=by
    let F':= z • ContinuousLinearMap.id ℂ (Alg m); let p:= F'.restrictScalars ℝ; change Sight _ _ _ _ _ (fun i=> _) _; refine ⟨fun X' W hv=> congr_arg (fun v:Alg m=> z • v) (hp.room _ _ hv),fun i=> Subalgebra.smul_mem _ (hp.gate _) z,fun Vξ h=> p.contDiff.contDiffAt.comp _ (hp.use Vξ h),fun Vξ h l hl hD=> ?_,hp.borel.const_smul z,mul_nonneg (norm_nonneg _) hp.travels⟩
    have hh:=left_linear p l (hp.use _ h) hl; change view _ _ (leftDerivs (z • Y) l Vξ) _ ≤_
    rw [show leftDerivs (z • Y) l Vξ=(z • leftDerivs Y l Vξ) from hh]; apply le_trans _ (mul_le_mul_of_nonneg_left (hp.pole Vξ h l hl hD) (norm_nonneg _)); unfold Plate.view; rw[mul_sum]; apply le_of_eq; apply sum_congr rfl; intro i _; rw[map_smul,norm_smul,mul_left_comm]
local notation "A₃" => hood o F R
local notation "Yj" => ycard o F R
local notation "Xd"=> sensor q o F W R
variable (h: Wage.Tip 6 o q F U t b w)(hB:R.Book o q)(hT:1 ≤ t)(V1:E→ℝ)(V2:K→ℝ)(r:ℝ)
variable (h₁:∀ i j, j∈ R.z i → Sight (oldZ R i) (o j) 2 U t (Reel.speaker q R i) (V1 i))(h₂:∀ i:K, ∀ x, ‖token c (ample 6 I) t (F.warp i x)‖ ≤ V2 i)
include h hT hB h₁ h₂
variable (hL:∀ i,|W i|≤r)(hk: ∀ i,separation (o i) (p (A'.unit_ i)) ≤ k)(hr:0 < r)
include hr hL hk
set_option maxHeartbeats 700000 in
lemma appearance : Setting A' (ycard o F R) (hatsF o F) q o p (oldZ R) (hood o F R k) (sensor q o F W R t) (spareK o F R V1 V2 r) U t:=by
     have hp(i): (Yj i).image o ⊆ road o F R i:=by
          rcases i with i|i; exact hB.stamp _; exact image_subset_iff.mpr (fun k hv=> (inside ..).1 ((mem_powerset.mp i.snd.2) hv))
     refine ⟨fun i=> subset_union_left,fun i=> subset_union_left,hp,fun i j hj=> ?_,fun i:E=>hB.stays i,?_,fun i U Vξ h=>?_,fun j=>studies q o F W h hT _,?_,?_,?_,?_⟩ -- V name conflict
     · obtain ⟨a,hk',rfl⟩:= mem_image.mp hj; obtain ⟨v,h',rfl⟩:=mem_image.mp hk'; exact mem_union_right _ (mem_biUnion.mpr ⟨v,h',halo_spec.mpr ⟨_,mem_singleton_self _,hk v⟩⟩)
     · rintro (i|i); exact (hB.permit i).const_smul (uvBirth W _); exact compactK q o F W h hT _ -- order
     · exact congr_arg (uvBirth W (R.z i) • ·) (hB.room i _ _ h)
     · rintro (i|i); intro Vξ; exact ⟨(hB.stage i Vξ).1.smooch _,(hB.stage i Vξ).2.scale _⟩; exact candles q o F W h hT _
     · rintro (i|i); intro U g; change parcelColor 6 g I (uvBirth W (R.z i) • (R.mark i _))=_; rw[map_smul,hB.tint]; try rfl
       exact phases q o F W h hT _
     · intro j x; change Stitch.Tablet.credits t (uvBirth W _ • _) ≤ r^_ * _; rw[Phy.spiceX]; let X':= sparkF q o F j x t; exact mul_le_mul (levelFunds W r hL _) ((brightK q o F h hT j x).trans (h₂ ..)) (Creek.load_nn ..) (pow_nonneg hr.le _)
     intro i j he; let z:= uvBirth W (R.z i); let f:= Reel.speaker q R i; have hy:pluck m (burst q (Yj (.inl i))) ∘ Xd t (.inl i)= z • f:=funext fun k'=>map_smul (pluck m (burst q (R.z i))) z (R.mark i k'); rw [hy]; let hF:= windV 2 (h₁ _ _ he) z; have hX: ‖z‖*V1 i ≤ spareK o F R V1 V2 r (Sum.inl i):=mul_le_mul_of_nonneg_right (levelFunds W r hL _) (h₁ i j he).travels; exact {hF with travels:= hF.travels.trans hX,pole:=fun s h H l u=> (hF.pole _ h H l u).trans hX} -- pole order.
end Gain
end YM.MassiveQCD.Sample.Eole
#print axioms YM.MassiveQCD.Sample.Eole.Gain.appearance
