import YM.Poised.Barr
import YM.Poised.Beryl
/-! # ap strings post.P.Full Price -/
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
variable (X:Support l)(Y:Support c)(b b':Cover) {u v w L:ℕ} {τ σ t vo vi A C :ℝ}
-- key readers. adapt crop
variable {X Y b b'} -- b now
variable (hΩ:Cruising (sliceL P h) X Y b b' u v)(H:TaperHol)(J:Labels.Jet su)
variable (d n) (vo t :ℝ)
variable (D':ℕ)(κ₁ κ₂:ℝ)
local notation "f0"=> craftT (X:=X) (b:=b) (b':=b') d n P h T J vo t
local notation "φ0"=> actionT (X:=X) (b':=b') (Y:=Y) d n P h T H J vo t
local notation "Ft"=>Pipes.purseX (wrap l b) D' vi -- may issue
-- typo namespace Chute open or Pipes.
variable {d n vo t κ₁ κ₂}
variable (hκ₁:0≤κ₁) (hκ₂:0 ≤ κ₂) (ht':0 ≤ t)(ht:t≤1)(hti:t ≤ 2*R.threshold)(hπ:vo ≤ A*vi)(hz':0 ≤ vo)(hz:0<vi)(hA:0≤A)
variable (hG:(∀ c (Y:Support c)(b x:Cover)(i:Axis), ‖transitL (visionL b H Y (t • J) n d) x i‖ ≤ κ₁*t*liftCost (d*d) (x-b)) ∧ ∀ (b x:Cover)(i:Axis), ‖verdict (paintL b (t • J) n d) x i‖ ≤ κ₁*t*liftCost (d*d) (x-b))
variable (hS:(∀ (c:Side)(b x:Cover)(i:Pipes.Shell) (j:ZBand d), ‖transitS (visionS (c:=c) d n H.T b vo) x i j‖ ≤ κ₂*vo*liftCost (d*d) (x-b)) ∧ ∀ (b x:Cover)(i:Pipes.Shell)(j:ZBand d), ‖paintS b vo n d (Place.seat x) i j‖ ≤ κ₂*vo*liftCost (d*d) (x-b))
def relicS (σ:ℝ)(d n:ℕ)(C:ℝ)(v:ℕ)(τ:ℝ) := (Fintype.card (ZBand d):ℝ)*(Fintype.card Pipes.Shell:ℝ)*(ore σ n C v*τ)
def relicG (σ:ℝ)(d:ℕ)(C:ℝ)(v:ℕ)(τ:ℝ) := 8*(ore σ d C v*τ)
def tar (σ:ℝ)(v:ℕ) := 2*Real.exp (-(σ/2)*v)
local notation "Fs" => relicS σ d (d*d) κ₂ v τ*A
local notation "Fg"=> relicG σ (d*d) κ₁ v τ
local notation "F's" => relicS (σ/2) d (d*d) κ₂ v τ*A
local notation "F'g"=> relicG (σ/2) (d*d) κ₁ v τ
local notation "t!"=> tar σ u
lemma ore_pos {σ C:ℝ}(h:0<σ)(hC:0≤ C) (n v :ℕ): 0≤ ore σ n C v:= by unfold ore; have h:=widthCost_ge h n; positivity
lemma relicS_pos {d n v:ℕ} (hσ:0<σ)(hC:0≤C)(hτ:0≤τ):0≤relicS σ d n C v τ:=by unfold relicS; positivity [ore_pos hσ hC n v]
lemma relicG_pos {d v:ℕ} (hσ:0<σ)(hC:0≤C)(hτ:0≤τ):0≤relicG σ d C v τ:=by unfold relicG; positivity [ore_pos hσ hC d v]
lemma widths (R:BudgetPoint)(i:Site l)(e:Edge (Site l)) : R.threshold ≤ width R i e:= by unfold width; exact le_mul_of_one_le_right R.threshold_pos.le (one_le_pow₀ (by simp))
private lemma canopy (x y:Pipes.Path l (ZBand d))(c s:ℝ)(hc:0 ≤ c)(hs:0 ≤ s)(hf:Sized c y.1 R (wrap l b))(hg: SeatD Ft (fun _=>1) y.2 s): Venture Ft (fun _=>1) (P:=R) (o:= wrap l b) (c+s) y:=
    ⟨⟨add_nonneg hc hs,fun i=> (hf.2 i).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hs) (width_pos ..).le)⟩,SeatD.less _ _ _ _ _ hg (le_add_of_nonneg_left hc)⟩
variable (hn:n≤d)(hk:4≤k)
variable (hσ:0<σ)(hτ:0 ≤τ) (hτT:T.R.A0.strip σ τ) (hSτ:∀ (u v:Pipes.Shell)(x:Cover),Width σ τ (arch P u v x))
local notation "cX"=> (wrap l b)
private lemma byKey (C:ℝ)(B:VectorD (Site l) (ZBand d))(hC:0≤C)(h:∀ (i:Faces (Site l)) j, ‖B i j‖≤ C*vo) (hS: 0≤ A) (hz:0<vi)(hπ:vo ≤ A*vi): SeatD Ft (fun _=>1) B ((Fintype.card (ZBand d):ℝ)*C*A):=by
    have ht (i:Faces (Site l)): vi ≤ Ft i:= le_mul_of_one_le_right hz.le (Heir.spine_one ..)
    apply (SeatD.from_weights _ _ _ _ (fun i=> hz.trans_le (ht i)) fun _=> zero_le_one).2; refine ⟨by positivity,fun i=>?_⟩
    simp only [one_mul]; apply (sum_le_sum fun j _=> h i j).trans; rw [sum_const,card_univ,nsmul_eq_mul]; let N:ℝ:=Fintype.card (ZBand d); change N*(C*vo) ≤ _; rw [← mul_assoc]; exact (mul_le_mul_of_nonneg_left (hπ.trans (mul_le_mul_of_nonneg_left (ht i) hS)) (by unfold N; positivity)).trans_eq (mul_assoc ..).symm
include hκ₁ ht' hσ hτ hΩ hG hτT hκ₂ hSτ hS hz' hA hπ hz hti
lemma giftT : Venture Ft (fun _=>1) (P:=R) (o:=cX) (Fg+Fs) f0 :=by
    refine canopy R D' 0 f0 Fg Fs (relicG_pos hσ hκ₁ hτ) (mul_nonneg (relicS_pos hσ hκ₂ hτ) hA) ?_ ?_ -- order проверить
    · have ho:=ore_pos hσ hκ₁ (d*d) v; refine ⟨relicG_pos hσ hκ₁ hτ,fun i=>?_⟩; unfold craftT forwardG; dsimp only; rw [Mom.screen_at]; split; swap; · rw [norm_zero]; exact mul_nonneg (relicG_pos hσ hκ₁ hτ) (width_pos ..).le
      next hi =>
         let G:= ore σ (d*d) κ₁ v * τ; have h0:0≤G:=by unfold G; positivity
         have hp:= (rice_p P h T hΩ _ hi.1 hσ (mul_nonneg hκ₁ ht') (hG.2 b') hτT i.2); refine hp.trans ?_
         have hw:t ≤ 2*width R cX i:= hti.trans (mul_le_mul_of_nonneg_left (widths ..) (by positivity))
         unfold relicG; apply le_trans (b:=4*t*G) ?_ ?_
         · unfold G ore; exact le_of_eq (by ring)
         unfold G at *; nlinarith only [hw,h0,mul_nonneg (sub_nonneg.mpr hw) h0]
    let C:=(Fintype.card Pipes.Shell:ℝ)*(ore σ (d*d) κ₂ v*τ)
    have hp:0 ≤ C:=by have h:=ore_pos hσ hκ₂ (d*d) v; unfold C; positivity
    rw [show Fs=(Fintype.card (ZBand d):ℝ)*C*A from (by unfold relicS C; ring)]; apply byKey _ _ f0.2 hp _ hA hz hπ; intro i k; obtain ⟨⟨x,j⟩,rfl⟩:= (Pipes.stretch (Site l)).surjective i
    change ‖asks (hiddenS X b (serve P (fun i=> paintS b' vo n d (Place.seat i)))) x j k‖≤ _; unfold hiddenS; rw [invers]; try dsimp only
    split; swap; · rw [show ‖(0:Flet (ZBand d)) j k‖=0 from (show ‖(0:ℂ)‖=0 from norm_zero)]; positivity
    next hx=>
       have he:=moss P h hΩ x hx hσ (mul_nonneg hκ₂ hz') (hS.2 b') hSτ j k -- defeq comp not obvious
       rw [Pi.smul_apply,Pi.smul_apply,norm_smul,ap_one,one_mul]; apply he.trans_eq; unfold C ore; ring
include hk hn
lemma graveT : Venture Ft (fun _=>1) (P:=R) (o:=cX) (t!*F'g+t!*F's) (φ0-f0):=by
    refine canopy R D' 0 _ _ _ (mul_nonneg (by unfold tar; positivity) (relicG_pos (half_pos hσ) hκ₁ hτ)) (mul_nonneg (by unfold tar; positivity) (mul_nonneg (relicS_pos (half_pos hσ) hκ₂ hτ) hA)) ?_ ?_
    · have h0 :0 ≤ t!*F'g:=mul_nonneg (by unfold tar; positivity) (relicG_pos (half_pos hσ) hκ₁ hτ)
      refine ⟨h0,fun i=>?_⟩; let G:= Heir.route T; change ‖Mom.screen X (Heir.route T _) i - forwardG _ _ _ i‖≤ _; rw [meetsG (b:=b) P h T ⟨σ,τ,hσ,hτT⟩]; unfold forwardG; rw [Mom.screen_at,Mom.screen_at]; split; swap; · rw [sub_zero,norm_zero]; exact mul_nonneg h0 (width_pos ..).le
      next hi=>
         have hr:= rice_left P h T hΩ _ hi.1 hσ (mul_nonneg hκ₁ ht') (hG.1 c Y b') (hG.2 b') hτT i.2 (fun i hi'=> glance hΩ hi.1 i hi' H _ hn)
         refine hr.trans ?_; apply le_trans (b:=(t/2)*(t!*F'g)) ?_ ?_; · unfold tar relicG ore; exact le_of_eq (by ring)
         rw [mul_comm]; exact mul_le_mul_of_nonneg_left (le_trans (by linarith : t/2 ≤ R.threshold) (widths ..)) h0
    let C:=t!*((Fintype.card Pipes.Shell:ℝ)*(ore (σ/2) (d*d) κ₂ v*τ)) -- remove factor groupling
    have hp:0 ≤ C:=by unfold C tar; have h:=ore_pos (half_pos hσ) hκ₂ (d*d) v; positivity
    rw [show t!*F's=(Fintype.card (ZBand d):ℝ)*C*A from (by unfold relicS C; ring)]; apply byKey _ _ _ hp _ hA hz hπ; intro i k; obtain ⟨⟨x,j⟩,rfl⟩:= (Pipes.stretch (Site l)).surjective i
    change ‖peel X _ _ k-hiddenS _ _ _ _ k‖≤ _; rw [revealedS X b,crowns P h hk]; change ‖asks (flats _) x j k- asks (flats _) x j k‖≤ _; rw [invers,invers]; try dsimp only
    split; swap; · rw [sub_self,norm_zero]; positivity
    next hx=>
       have he:=moss_left P h hΩ x hx hσ (mul_nonneg hκ₂ hz') (hS.1 c b') (hS.2 b') hSτ j k (fun i hi'=> spinward hΩ hx i hi' d n H.T vo hn) -- implicit launch
       rw [Pi.smul_apply,Pi.smul_apply,Pi.smul_apply,Pi.smul_apply,← smul_sub,norm_smul,ap_one,one_mul]; apply he.trans_eq; unfold C ore tar; ring
end Chute
end YM.Massive.Poised
#print axioms YM.Massive.Poised.Chute.giftT
#print axioms YM.Massive.Poised.Chute.graveT
