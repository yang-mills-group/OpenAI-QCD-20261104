import YM.Patria.Odors
import YM.Patria.Reflect
/-! Moment symmetry, share precision for all gauges. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace YM.Massive.Patria.Canvas
open Filter Function Set MeasureTheory Lattice Source RG Wilson Source.Drops
open scoped Matrix.Norms.Frobenius BigOperators Topology Matrix ContDiff Classical
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead
variable {B : Type*} {d:ℕ}
open QCD.Revolve TorusPCAC.Geometry Lining Lining.Ferry Lining.Temper
open Poised Beacon Finset
variable (s:Signed)(H:TaperHol){c:Side}(p:EuPin)(b x:Cover)(v:ℝ)
variable (u:FlavorTorus)(Y:Density c 6)(J:Labels.Jet su)(a:Axis)(hp:p.Lifts s)(hc:18≤ c.val)
local notation "Φ"=> Beacon.glow (c:=c) (d:=d) H.T 0 v
local notation "φ"=> Beacon.moment (d:=d) H 0 J
lemma glow_basis (M:Spike) (he:18≤c.val) : Action.moved 1 M*Φ=Φ*spinTable M:=by rw [under_spin]; exact spin_motion 1 H 1 v M he (map_one Signed.inclusionO).symm
lemma glow_flip (he:18≤ c.val)(M:Spike) : Action.moved (Signed.mirror a) M*Φ= Φ*flipTable a M:=by obtain ⟨p,hp⟩:= EuPin.choice (Signed.mirror a); rw [hem_turn _ hp]; exact spin_motion _ _ _ _ _ he hp
lemma glow_rim : UV.Mstar (Φ)=Φ:=by
    ext i j; simp only [mstar,Beacon.glow,Matrix.of_apply]; split
    next he=> simp only [spun,star_mul,ap_star, profile]; push_cast;  simp [mul_comm,mul_left_comm,mul_assoc] -- simp
    next he=> rw [star_zero]
include hp hc in
lemma spin_seen : let M:=adapter (UV.turned (d:=d) p (wave p.matrix⁻¹.val)) (UV.turned p (wave p.matrix.val.transpose)); moment (d:=d) H 0 J (Action.pin p s Y) v=M (moment (d:=d) H 0 (JQ s J) Y v):=by
    intro M; unfold Beacon.moment Action.pin; rw [current_read,reads s H d _ v hc,← current_read,adapt_together]; unfold M; rw [adapt_together]; congr 2 <;> exact spin_motion (d:=d) s H p v _ hc hp
include hc in
lemma charge_seen : moment (d:=d) H 0 J (Action.charge Y) v= changeVars (masq d) (moment H 0 (Labels.changedJet (fun _=> UV.recolor) J) Y v):=by
    unfold Beacon.moment Action.charge; rw [current_read, midnight, ←current_read]; unfold adapter; rw [multipleChange,multipleChange]; congr 2 -- block
    simp only [masq,Matrix.fromBlocks_multiply,Matrix.mul_zero,Matrix.zero_mul,add_zero,zero_add]; congr 1 <;> exact glow_basis H v _ hc
include hc in
lemma eye_seen : moment (d:=d) H 0 J (Action.adj a Y) v= aSpin d a (moment H 0 (JQ (Signed.mirror a) J) Y v):= by
    unfold aSpin; simp only [LinearMap.comp_apply,AlgHom.toLinearMap_apply]
    unfold Beacon.moment Action.adj; rw [current_read, reads _ H d _ v hc,← current_read]; unfold adapter; rw [dagger_change,multipleChange,multipleChange,mstar_diag]; apply congr_arg (fun x=>changeVars x _); unfold eyeW; simp only [Matrix.fromBlocks_multiply,Matrix.mul_zero,Matrix.zero_mul,add_zero,zero_add]; rw [glow_rim]; congr 1 <;> exact glow_flip H v a hc _
lemma slash_pig : moment (d:=d) H 0 J (Action.flavor u Y) v= adapter (byFlavor u (fun i:SpinMode d=>i.2)) (byFlavor u⁻¹ (fun i:SpinMode d=>i.2)) (φ Y v):=by
    let D (x:FlavorTorus) : Matrix (SpinMode d) (SpinMode d) ℂ := byFlavor x Prod.snd
    have hf(x: FlavorTorus) : phaseD c x*Φ= Φ*D x:=by rw [indeed]; exact nacre_flavor _ x
    change adapter _ _ (adapter (phaseD c u) (phaseD c u⁻¹) (Y _))= adapter (D u) (D u⁻¹) (adapter _ _ (Y _)); rw [adapt_together,adapt_together]; congr 2
    exact hf u
    exact hf u⁻¹
lemma grade_seen : moment (d:=d) H 0 J (Action.parity Y) v= grade (φ Y v):= by unfold Action.parity Beacon.moment; exact Eq.symm (Grass.exterior_parity (substitution _) _) -- maybe
-- Real movement. Anchor key tests.
def shifter (c:Side)(b:Cover):= copies 6 (hues (wrap c b) 1 (heat b) 1)
lemma heat_rim : UV.Mstar (shifter c b) = shifter c b:=by ext i j; rcases signs (n:=c) (sheet i.1.1+b) with h|h <;> unfold shifter <;> have he:=h <;> change heat b i.1.1=_ at he <;> simp only [mstar,Lat.copies,hues,Matrix.blockDiagonal_apply,rides,Matrix.of_apply,Matrix.smul_apply,star_one,wave_one, he, heat] <;> split_ifs <;> by_cases hh:i.1.2=j.1.2 <;> simp [Matrix.one_apply,hh]
lemma shreds : shifter c b * Beacon.glow H.T (x+b) v= Beacon.glow (d:=d) (c:=c) H.T x v:=by
    let p:= fun x:Site c=> x+ wrap c b; have he : shifter c b=spar p (fun x=>heat b x • 1):=by ext i j; by_cases he:i.2=j.2 <;> by_cases hp:p i.1.1=j.1.1 <;> simp only [p] at * <;> simp [shifter,spar_intro,Matrix.blockDiagonal_apply, wave_one,p, copies,hues, rides,shiftE,he,hp,Signed.actEquiv,Signed.act_one]
    rw [he,indeed,indeed]; refine Eq.trans (spar_mul p (fun x=> heat b x • 1) _) (congr_arg nacre (funext fun i=>funext fun j=>?_)); rw [Matrix.smul_mul,Matrix.one_mul, show offset (x+b) (p i)= offset x i from ?_,smul_smul]; swap
    · unfold p Beacon.offset; rw [map_add,add_sub_add_right_eq_sub]
    let W:= Beacon.offset x i; let u:= W+x; have hu: wrap c u=i:=by simp [u,W,Beacon.offset]
    have hx: spun H.T (x+b) (p i)= heat b i * spun H.T x i:=by
        unfold p spun; simp only [Beacon.offset,map_add,add_sub_add_right_eq_sub]; change _*(ap c (W+(x+b)))=_*(_*ap c u); rw [← add_assoc]; have hψ: ap c (W+x+b)= heat b i*ap c u:=by nth_rw 1 [← hu]; exact heated b u
        rw [hψ, mul_left_comm]
    rw [hx, mul_assoc (heat b i),← mul_assoc (heat b i), show heat b i*heat b i=1 from thermal_norm _,one_mul]
lemma paper_cut : pull 1 (wrap c b) (Beacon.current (c:=c) H (x+b) d J v)= Beacon.current H x d J v:=by funext i; rw [pull_one]; simp [Lattice.translate,Beacon.current,Beacon.views,Beacon.offset]
lemma shift_seen : moment (d:=d) H (x+b) J (march b Y) v= moment H x J Y v:=by
   unfold Beacon.moment march post crank Kit.disguise; rw [paper_cut, adapt_together]; let x' := Y (Beacon.current H x d J v); change adapter (shifter c b*Beacon.glow H.T (x+b) v) (Mstar (shifter c b)*Beacon.glow H.T (x+b) v) x'= adapter _ _ x'; rw [heat_rim]; congr 2 <;> exact shreds H b x v
end YM.Massive.Patria.Canvas
#print axioms YM.Massive.Patria.Canvas.heat_rim
#print axioms YM.Massive.Patria.Canvas.shift_seen
