import YM.Poised.Rings
/-! # passage to polynomial read of actual.Com.Channels, including omitted parity. Weighted output root anchored in forward support. Price per panel. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Poised
open Function Filter Set Lattice Wilson Tree RG Source Source.Drops MeasureTheory Finset WardBin Work.G05 Planned.PrimaryIntegral295 Planned.PrimaryIntegral295.Place
open scoped Topology BigOperators ContDiff Matrix.Norms.L2Operator TensorProduct Classical ComplexConjugate
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead
variable {B : Type}{d k j n:ℕ}{c l:Side}
namespace Chute
open Pipes QCD.Kit QCD.Flume QCD.Cove QCD.Creek QCD.Loom QCD.Flume QCD.Fork QCD.Port QCD.Brick Lining Lining.Ferry
open Precision Pressure Garden Run Laurent Carrier Next.Free QCD.Kit
open PhysicalNext.JointLoad Palette Steed Beacon MultiNext.SignedSource Cruising MultiNext.SignedSource.Lyre
variable {K: KernelChoices}(P:Flight j k)(h:l.val=c.val*P.L.val)(T:Tube su (Flight.visit P K h)) (R:BudgetPoint)
variable {X:Support l}{Y:Support c}{b:Cover} {u v L:ℕ} {τ t vo A C q:ℝ}
open Kites Fountain MassiveQCD.Plate Costs Display Next.Foundations PhysicalNext.Repeat PhysicalNext.Repeat.Brim
lemma visor {F:Grid c → Lat.Fields c 6}(h:ContDiffAt ℝ n (F∘increment 1) 0)(Z:Support c):ContDiffAt ℝ n ((F ∘ splitF Z) ∘ increment 1) 0:=by
    rw [show (F∘ splitF Z) ∘ increment 1 = (F ∘ increment 1) ∘Mom.screen Z from funext fun i=>congr_arg F (split_inc i)]; exact (show ContDiffAt ℝ (n:WithTop ℕ∞) _ (Mom.screen (G:=su) Z 0) from (map_zero (Mom.screen (G:=su) Z)).symm ▸ h).comp _ (Mom.screen Z).contDiff.contDiffAt
lemma onpiece(F:Grid c → Lat.Fields c 6)(Z:Support c)(h:LocalOn Z F): F=F∘splitF Z:= funext fun i=>h _ _ fun j hj hi=> (if_pos (show Mom.needed Z j from ⟨hj,hi⟩)).symm
private lemma diff_diag {F Z:Grid c→Lat.Fields c 6}(r:ℕ)(α:Directions su c)(hf:ContDiffAt ℝ r (F∘increment 1) 0)(hg:ContDiffAt ℝ r (Z∘increment 1) 0): leftDerivs (F-Z) (List.replicate r α) 1=leftDerivs F (List.replicate r α) 1-leftDerivs Z (List.replicate r α) 1:=by
   simp_rw [diagnosis α]
   have h : ContDiffAt ℝ r (F ∘ increment 1 ∘ rod α) 0:=(show ContDiffAt ℝ (r:WithTop ℕ∞) (F∘ increment 1) (rod α 0) from (map_zero (rod α)).symm ▸ hf).comp _ (rod α).contDiff.contDiffAt
   have g : ContDiffAt ℝ r (Z ∘ increment 1 ∘ rod α) 0:=(show ContDiffAt ℝ (r:WithTop ℕ∞) (Z∘ increment 1) (rod α 0) from (map_zero (rod α)).symm ▸ hg).comp _ (rod α).contDiff.contDiffAt
   exact DFunLike.congr_fun (iteratedFDeriv_sub_apply h g) (fun _=>1)
variable (J:Labels.Jet su)(H:TaperHol)(F:Grid c→Lat.Fields c 6)(Z:Grid c → Lat.Fields c 6)(hY: LocalOn Y F)(hF:ContDiffAt ℝ d (F ∘ increment 1) 0)(hZ:ContDiffAt ℝ d (Z∘ increment 1) 0)(o:Site c)(ho:o∈Y)(hk:coverNumber (radiusB τ) Y≤ radiusB τ) (hm :separation o (wrap c b)≤ u)
variable (E':Side)(hα:R.threshold ≤2*fiery su τ E') (hp:R.power=L)(ht': d*d ≤ R.power)(D':ℕ)(hD :surface d ≤ D')(hx:0<t)
local notation "r"=> wrap c b
variable (hC:0≤C)(hψ:∀ i≤d,∀ α: Directions su c, R.dirBound o α → ‖α‖ ≤ canopyW su E' R.power τ → ‖leftDerivs ((framesF (purseX o D' t)) ∘ F) (List.replicate i α) 1-leftDerivs ((framesF (purseX o D' t))∘Z) (List.replicate i α) 1‖≤ C)
def rayE (d n:ℕ)(v:ℝ)(H:TaperHol)(b:Cover)(J:Labels.Jet su)(F: Grid c→Lat.Fields c 6):SpinPol d:= iteratedDeriv n (engine v (ZBand d)∘Beacon.moment H b J F) 0
lemma quietT (hT:ActionTest (d:=d) H b F 0)(i:ℕ)(hi:i≤d):rayE d i t H b J F=0:=by
    let Y:=Beacon.moment H b (d:=d) J F; let K:=((engine t (ZBand d)).toLinearMap.restrictScalars ℝ).toContinuousLinearMap; change iteratedDeriv i (K∘Y) 0=_; rw [Display.clm_step Y i 0 ((hT J).1.of_le (Nat.cast_le.mpr hi)),show iteratedDeriv i Y 0=0 from ?_, map_zero]; rw [(hT J).2.2 i hi, ← funext (observe J (0:Pol d)), order_test,map_zero,map_zero,smul_zero]
lemma faithfulQ(p:Pol d)(hT : ActionTest H b F p)(i:ℕ)(hi:i≤d): rayE d i t H b (q • J) F= (i.factorial:ℂ) • ready d J (geometry i (Sieve.widths q t p)):=by
   let Y:=Beacon.moment H b (d:=d) (q • J) F; let K:=((engine t (ZBand d)).toLinearMap.restrictScalars ℝ).toContinuousLinearMap; change iteratedDeriv i (K∘Y) 0=_; have hX:=hT (q • J); rw [Display.clm_step Y i 0 (hX.1.of_le (Nat.cast_le.mpr hi)), show iteratedDeriv i Y 0=iteratedDeriv i (fun t=> desired p (q • J) t) 0 from hX.2.2 _ hi,← Display.clm_step _ i 0 (hX.2.1.of_le (Nat.cast_le.mpr hi)),←order_test]; apply congr_arg (fun X=> iteratedDeriv i X 0); funext v; rw [Sieve.countingG,observe]; rfl
include hZ hF
lemma ray_sub (hn:n≤d): rayE d n t H b J (F-Z)=rayE d n t H b J F-rayE d n t H b J Z:=by
   obtain ⟨V,-,h⟩ :=obtainsD H b F hF; obtain ⟨U,-,hu⟩:=obtainsD H b Z hZ
   let K:=((engine t (ZBand d)).toLinearMap.restrictScalars ℝ).toContinuousLinearMap; unfold rayE; let Q:= Beacon.moment H b J Z (d:=d); let P:= Beacon.moment H b J F (d:=d); change iteratedDeriv n _ 0= iteratedDeriv n (K∘ P) 0-iteratedDeriv n (K∘ Q) 0; rw [show engine t (ZBand d) ∘ Beacon.moment H b J (F-Z)=fun u=> K (P u)-K (Q u) from ?_]; swap; · funext x; change K (changeVars _ (F _-Z _))= _; rw [map_sub,map_sub]; rfl
   exact iteratedDeriv_fun_sub (K.contDiff.contDiffAt.comp _ ((h J).1.of_le (Nat.cast_le.mpr hn))) (K.contDiff.contDiffAt.comp _ ((hu J).1.of_le (Nat.cast_le.mpr hn)))
include R hα hY hm hk ho hp ht' hx hD hC hψ
def ruleUp (d L D' u:ℕ) := penny d*((1+(u:ℝ))^D'* ((1+(u:ℝ))^L)^d) -- incorrect move factor exponent
lemma organ (hn:n≤d) : let X:= F- Z ∘ splitF Y; let M:= (1+(u:ℝ)); let K:=(stageZ H c b t (d:=d)); let P':=K∘ X
    ∀ i≤d,∀ α:Directions su c,R.dirBound (wrap c b) α → ‖leftDerivs P' (List.replicate i α) 1‖ ≤ (penny d*(M^D'* (M^L)^d))*C :=by
   intro X M K P' i hi α hα'; let D:=purseX o D' t; let V:= framesF D; let X':=F ∘splitF Y-Z∘splitF Y; have hg:X=X':=congr_arg (·-Z∘splitF Y) (onpiece F Y hY); have hX: ContDiffAt ℝ (d:WithTop ℕ∞) (X∘ increment 1) 0:=hF.sub (visor hZ Y); let s:= List.replicate i α; let L':=(K.restrictScalars ℝ).toContinuousLinearMap; change ‖leftDerivs (L' ∘ X) s 1‖≤ _; let v:= leftDerivs X s 1; have hs:s.length ≤ d:=(List.length_replicate ..) ▸ hi; rw [Push.Local.left_linear _ _ hX hs]; change ‖L' v‖ ≤ _; apply (lots H.T b t v hx.le hD).trans
   rw [mul_assoc]; have ht:0≤penny d:=by unfold penny; positivity; --guard
   apply mul_le_mul_of_nonneg_left _ ht; apply (march_view c o r v _ _ hx).trans
   have hv:F ∘ splitF Y= F:= (onpiece F Y hY).symm
   have hy:(V ∘ X)=((V ∘F)-(V∘Z))∘splitF Y:= by rw [hg]; exact funext fun i=> map_sub V _ _; --guard
   suffices h:‖framesF D v‖≤ (M^R.power)^d*C by rw [hp] at h; change (1+(separation o r:ℝ))^D'*‖framesF D v‖≤_; rw [mul_assoc]; exact mul_le_mul (pow_le_pow_left₀ (by positivity) (by exact add_le_add_right (Nat.cast_le.mpr hm) _) _) h (norm_nonneg _) (by unfold M; positivity)
   unfold v; rw [←Push.Local.left_linear _ _ hX hs,show (framesF D) ∘ X=_ from hy]
   have he:ContDiffAt ℝ (d:WithTop ℕ∞) ((V∘F) ∘increment 1) 0:= V.contDiff.contDiffAt.comp _ hF; have hE:ContDiffAt ℝ (d:WithTop ℕ∞) ((V∘Z) ∘increment 1) 0:= V.contDiff.contDiffAt.comp _ hZ; refine shiftD _ R _ _ τ E' C hC (he.sub hE) ?_ hk hm hα ho α hα' hi; intro i hi v hV hq; rw [diff_diag _ _ (he.of_le (Nat.cast_le.mpr hi)) (hE.of_le (Nat.cast_le.mpr hi))]; exact hψ i hi v hV hq
omit R hα hY hm hk ho hp ht' hx hD hC hψ hF hZ
-- quantify all charges post.B.C.
lemma oracle (d n E Pk D' :ℕ)(J: Labels.Jet su)(hn:n≤d):∃ C:ℝ,0≤ C ∧ ∀ (c:Side)(F Z : Grid c→ Lat.Fields c 6) (Y:Support c)(o :Site c)(H:TaperHol)(b:Cover)(R:BudgetPoint)(L:Side)(x D t:ℝ), LocalOn Y F→ ContDiffAt ℝ d (F∘increment 1) 0 → ContDiffAt ℝ d (Z∘ increment 1) 0 → o ∈Y → coverNumber (radiusB x) Y ≤ radiusB x → separation o (wrap c b) ≤ E→R.threshold ≤ 2 * fiery su x L → R.power=Pk → surface d ≤D' → d*d ≤ R.power →0<t → 0≤D → (∀ i≤d,∀ α:Directions su c,R.dirBound o α→ ‖α‖ ≤ canopyW su L R.power x → ‖leftDerivs (framesF (purseX o D' t)∘ F) (List.replicate i α) 1-leftDerivs (framesF (purseX o D' t)∘ Z) (List.replicate i α) 1‖ ≤ D) → ‖rayE d n t H b (R.threshold • J) F - rayE d n t H b (R.threshold • J) (Z ∘ splitF Y)‖ ≤ C*D:=by
    obtain ⟨C,hC,h⟩:= curvatureD d n J hn; let W:= penny d*((1+(E:ℝ))^D'*((1+(E:ℝ))^Pk)^d); have hW:0≤W:=by unfold W penny; positivity
    refine ⟨C*W,mul_nonneg hC hW,?_⟩; intro l F Z Y o H b R L x D t hY hF hZ ho hx hS hθ hp hβ ht ht' hD he; rw [← ray_sub (R.threshold • J) H F (Z∘ splitF Y) hF (visor hZ _) hn,mul_assoc]
    let g:= F-Z∘splitF Y; let L':= ((stageZ (d:=d) H l b t).restrictScalars ℝ).toContinuousLinearMap; apply h l g b H R t (W*D) (mul_nonneg hW hD) ht (show ContDiffAt ℝ d ((L'∘ g) ∘ increment 1) 0 from L'.contDiff.contDiffAt.comp _ (hF.sub (visor hZ _)))
    exact organ R H F Z hY hF hZ o ho hx hS L hθ hp ht D' hβ ht' hD he hn
-- h needed. Need reusable estimate radi.T
end Chute
end YM.Massive.Poised
#print axioms YM.Massive.Poised.Chute.organ
