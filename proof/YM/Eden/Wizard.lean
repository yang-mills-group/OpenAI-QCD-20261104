import YM.Eden.Hue
/-! # charging at all the actions. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Eden
open Function Lattice Laurent Bloch Metric RG Filter Arise Arise.Range
open Finset YM.Bank Precision Matrix
open scoped Topology BigOperators Matrix Matrix.Norms.Frobenius Classical Kronecker
open QCD QCD.Lat QCD.Free QCD.Flume QCD.Bank Next.Free
open QCD.Creek QCD.Anomaly QCD.Cove QCD.Kit QCD.Bloom QCD.Pine QCD.Grass
open Massive Massive.UV Patria Patria.Exposure Revolve TorusPCAC.Geometry TorusPCAC.Geometry.AxisB
open Lining Ferry Cylinder Elm Elm.SparK Elm.SparK.Arbor
variable {c f:Side}{N k m:ℕ}{I J:Type}[Fintype I][Fintype J]
variable (W:Walk)(p:Multi k)(x y: Cover) (U: Grid c)(s:Signed)(P: EuPin)(A: Spike)(g: Lat.Frame c)
local notation "CU"=> conjugate ∘ U
local notation "Q"=> rollsU k x U
local notation "Fʼ"=> fadeF x U
lemma night_b (j:Site c) : bladeU x (CU) p j=Mstar (bladeU x U p j):=by
    let X:= CU; have ht(W:Walk): fadeF x X W j=Mstar (Fʼ W j):=by
        unfold fadeF; split; next he=>
           rw [show haloW c x W X = TorusPCAC.Stencil.conjSU (haloW c x W U) from Reflection.roadmap ..]; rw [show colour (TorusPCAC.Stencil.conjSU _)=(Mstar (colour (haloW c x W U))) from rfl, mstar_smul, mstar_touch, Ferry.ap_star]
        next=>rw [mstar_sq,star_zero,transpose_zero]
    unfold bladeU hears; simp only [Finsupp.linearCombination_apply,Finsupp.sum,mstar_sq,star_sum, Matrix.transpose_sum]; refine sum_congr rfl (fun i _=> ?_); rw[ht,mstar_sq,star_smul, Matrix.transpose_smul]; rfl
lemma nova : rollsU k x (CU)=Mstar Q:=by unfold rollsU; rw[mark_star, show bladeU x (conjugate ∘ U) (k:=k)= _ from funext fun i=>funext fun j=> night_b i x U j]
lemma roll_pinO(h:P.Lifts s): Mstar (rollsU k x (pull s 0 U))*Action.moved s A= UV.turned P (wave A)*Mstar (rollsU k (s.act x) U):=by rw [← nova,← nova, show conjugate ∘ pull s 0 U=pull s 0 (conjugate ∘ U) from (by funext i; unfold pull; simp only [Function.comp_apply]; unfold Step.read; split; simp [Papyrus.conj_rev]; rfl), roll_pin x (CU) s P A h]
noncomputable abbrev pinTT (k:ℕ)(s:Signed) (P:EuPin): Matrix (Pairs (SpinMode k)) (Pairs (SpinMode k)) ℂ:= Matrix.fromBlocks (UV.turned P (wave P.matrix⁻¹.val)) 0 0 (UV.turned P (wave P.matrix.val.transpose))
lemma motionM(h:P.Lifts s): mood k x (pull s 0 U)* PinWheel c s P=pinTT k s P*mood k (s.act x) U:=by unfold mood PinWheel slab; rw [show Mstar (Action.moved (n:=c) (F := 6) s P.matrix⁻¹.val)= Action.moved s P.matrix.val.transpose from (by rw [← star_eu,dir_sail,mstar_sq,star_star])]; unfold pinTT; rw[fromBlocks_multiply, fromBlocks_multiply]; simp only [Matrix.mul_zero,Matrix.zero_mul,add_zero,zero_add]; exact congr_arg₂ (fun X Y: Matrix (SpinMode k) (Modes c 6) ℂ=> fromBlocks X 0 0 Y) (roll_pin x U _ _ _ h) (roll_pinO x U _ _ _ h)
lemma festiveV (a:Axis):Mstar (mood k x (pull (Signed.mirror a) 0 U))*moonS c a = eyeW k a*mood k ((Signed.mirror a).act x) U:=by
     obtain ⟨P,hp⟩:= EuPin.choice (Signed.mirror a); unfold moonS eyeW mood slab; rw [mstar_diag, mstar_again, fromBlocks_multiply, fromBlocks_multiply]; simp only [Matrix.zero_mul, Matrix.mul_zero,add_zero,zero_add]; rw [hem_turn a hp,hem_turn a hp]; exact congr_arg₂ (fun (X Y: Matrix (SpinMode k) (Modes c 6) ℂ)=>fromBlocks 0 X Y 0) (roll_pinO x U _ _ _ hp) (roll_pin x U _ _ _ hp) -- find sig
lemma reel_char : mood k x (CU)*railN c= masq k * mood k x U:=by
     unfold railN mood slab masq; rw[fromBlocks_multiply,fromBlocks_multiply]; simp only [Matrix.zero_mul, Matrix.mul_zero,zero_add,add_zero]; rw[nova,mstar_again]
     let M:=chargeMatrix; have hh: EuPin.Lifts 1 1:=(map_one Signed.inclusionO).symm; let Z:=-(chargeMatrix⁻¹).transpose
     change _= _; rw [under_spin chargeMatrix,under_spin Z]; let h1:= roll_pin (k:=k) x U 1 1 Z hh; let h2:= roll_pinO (k:=k) x U 1 1 M hh; rw [pull_id,Signed.act_one] at h1 h2; exact congr_arg₂ (fun X Y: Matrix (SpinMode k) (Modes c 6) ℂ=>fromBlocks 0 X Y 0) h2 h1 -- order check
-- gauge & flavor
lemma gradient (j:Site c): bladeU x (Lattice.gauge g U) p j*touch (colour (g j))= touch (colour (g (wrap c x)))*bladeU x U p j:=by
    unfold bladeU hears; simp only [Finsupp.linearCombination_apply,Finsupp.sum,Matrix.sum_mul,Matrix.mul_sum,Matrix.smul_mul,Matrix.mul_smul]; refine sum_congr rfl (fun i _=>?_); apply congr_arg; unfold fadeF; split
    next h => let T:= landsE c x i; let Z:=haloW c x i U; let Y:=g T; rw [h,halo_change, Matrix.smul_mul,Matrix.mul_smul]; congr 1; rw[Lat.touch_mul, Lat.touch_mul]; apply congr_arg; simp [Lat.colour_mul,mul_assoc, Lat.colour_inv]; rw [show star (colour (g (landsE c x i)))* colour _ =1 from su.mat_star_mul _, mul_one] -- find
    next=> rw[Matrix.zero_mul,Matrix.mul_zero]
lemma gradient_m : mood k x (Lattice.gauge g U)*slab (Lat.rotates 6 g)=noir (g (wrap c x)) k * mood k x U:=by
    have h : rollsU k x (Lattice.gauge g U)*Lat.rotates 6 g = colorTable (g (wrap c x))*Q:=by
       rw [rollsU, Ferry.sight, eye_color]; let X(i:Multi k):= bladeU x (Lattice.gauge g U) i; let Z(i:Multi k):= bladeU x U i
       exact (Lining.spar_after (Equiv.refl _) (fun i=> touch (colour (g i))) X).trans ((congr_arg nacre (funext fun i=> funext fun j=> gradient ..)).trans (Lining.spar_mul id _ Z).symm) -- id
    unfold mood slab noir; rw [← mstar_sq]; rw [fromBlocks_multiply,fromBlocks_multiply]; simp only [Matrix.mul_zero,Matrix.zero_mul, add_zero,zero_add,h,← mstar_mul]
    rfl
lemma festival (u:FlavorTorus): mood k x U*slab (flavP c u)= slab (byFlavor u (Prod.snd (α:= Multi k × Fiber))) * mood k x U:=by
    have h : rollsU k x U * (flavP c u)= byFlavor u Prod.snd * Q := (nacre_flavor _ _).symm
    unfold mood slab; rw[fromBlocks_multiply,fromBlocks_multiply]; simp only [Matrix.mul_zero,Matrix.zero_mul,add_zero,zero_add,h,← mstar_mul]; rfl
end YM.QCD.Eden
#print axioms YM.QCD.Eden.motionM
#print axioms YM.QCD.Eden.festiveV
