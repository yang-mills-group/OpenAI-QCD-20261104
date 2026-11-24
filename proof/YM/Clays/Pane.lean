import YM.Clays.Reeds
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Sample
open QCD QCD.Grass QCD.Cove Lattice Finset Ribbon Cupola Stew
open Function Lattice Wilson Creek Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph QCD.GasP PhysicalNext.Repeat.Turn Patron Kites Ribbon Cupola Plate Plate.Card Relight Ruby Massive.PCAC
open scoped Topology BigOperators ContDiff Classical Matrix Matrix.Norms.L2Operator
namespace Basal
variable {c L:Side}{N B i j k n F:ℕ}{I D:Type}[Fintype I] {A2 T2 Ae At M W0 X:ℝ}{a C t b w x v θ η ξ z m:ℝ}
-- old core price n. use T2:unscaled radius-independent upper combined given ∥r_j,w∥ ≤ τ.K.μ.L.Width. Requires salary≤1. Ɛ orientation rows. ζ tolerance.
local notation "μ0"=> (1/8:ℝ)
local notation "u1"=> (24/256:ℝ)
local notation "α1"=> (25/256:ℝ)
local notation "ε"=> (1/256:ℝ)
local notation "rP"=>riseP i j B ε u1
open Stags Footprint Push.AbsoluteSums.Reserves
local notation "bP"=>Stags.bonus F B ε
local notation "Bp"=>absP B k n F ε (C*ξ)
local notation "Bu"=>anth ε (α1+2*ε) B
local notation "ΔE" x:arg=> Bp*(Bu*x)
local notation "t!"=> absP B k n F ε C
noncomputable def pledgeP (B k n F:ℕ)(C Ae At T2:ℝ):= absP B k n F (1/256) C * (anth (1/256) (25/256+2*(1/256)) B * (Ae+At)+ (Stags.bonus F B (1/256)*T2+1))
local notation "b₀"=> Real.exp (u1-μ0)
local notation "Xp"=> pledgeP B k n F C Ae At T2
-- huge finite reaches after sampling. cost ∼ v² NO g besides powers of pre radius B.W acres
noncomputable def growthP (B k n F i j:ℕ)(T2 Ae At C θ z:ℝ):ℝ:=
    let Z:= pledgeP B k n F C Ae At T2
    let w:= riseP i j B ε u1*Z
    1+(1-b₀)⁻¹*Z+(w+θ*(z*w)+z*w)*(1+Stags.bonus F B (1/256))+Z+256*(hullP B F*C)
local notation "GP"=>growthP B k n F i j T2 Ae At C θ z
local notation "vF"=> (At*v^2)
local notation "T₀"=> bP * T2 * X + X
local notation "UP"=> ΔE Ae +ΔE (vF)+Bp*(Stags.bonus F B ε*(T2*X)+X)
local notation "Cp"=>rP* (UP)
variable (hθ:1 ≤ θ)(hz:1 ≤ z)(he:0 ≤Ae)(ha:0 ≤ At)(hc:0 ≤ C)(hK:0 ≤ T2)
variable (B)
lemma earnA (a:ℝ):0≤anth ε a B:=by unfold anth payment degreeIncome; have h:0 ≤1-Real.exp (-ε):=sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by norm_num)); positivity
lemma earnB (H:ℕ):0 ≤ Stags.bonus H B ε:=by unfold Stags.bonus payment degreeIncome; have h:0 ≤1-Real.exp (-ε):=sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by norm_num)); positivity
private lemma upsilon : 0 < 1-b₀ := by apply sub_pos.mpr; exact Real.exp_lt_one_iff.mpr (by norm_num)
variable {B}
include hθ hz he ha hc hK
lemma etaP : 1≤GP:=by
    have hr:0 ≤rP:=by unfold riseP polyPrice; positivity
    have hb:0 ≤ bP:=earnB ..; have hk:t! ≥0:=by unfold absP polyPrice hullP roy; positivity
    have he':0 ≤Xp:=by unfold pledgeP; exact mul_nonneg hk (add_nonneg (mul_nonneg (earnA ..) (add_nonneg he ha)) (add_nonneg (mul_nonneg hb hK) zero_le_one))
    let w:=rP*Xp; have hw:0 ≤ w:=mul_nonneg hr he'; have hu: 0≤ hullP B F*C:=by unfold hullP; positivity
    have hv:0 ≤(1-b₀)⁻¹:= (inv_pos.mpr upsilon).le
    change 1 ≤1+_+(w+θ*(z*w)+z*w)*(1+bP)+Xp+_; apply le_trans (le_trans (le_trans (le_add_of_nonneg_right (mul_nonneg hv he')) (le_add_of_nonneg_right ?_)) (le_add_of_nonneg_right he')) (le_add_of_nonneg_right (mul_nonneg (by norm_num) hu)); positivity
variable (hv:1 ≤ v) (hx:0 ≤ X)(hX:X ≤ 1)(hξ:0 ≤ ξ)(hr:ξ*(growthP B k n F i j T2 Ae At C θ z*v^2) ≤ X)
include hv hx hX hξ hr
lemma healthyP: hullP B F*(C*ξ) ≤ ε ∧ b₀ * X + UP ≤ X ∧ ΔE vF ≤1 ∧ 0 ≤ UP ∧ bonus F B ε * (Cp+θ*(z*(Cp))) ≤1 ∧ (z*Cp ≤ ξ*(GP*v^2))∧ (1+θ*z)*Cp ≤ ξ*(GP*v^2):=by
    let R:= t!; have hb:0≤bP:= earnB ..; have hT:0≤ R:=by unfold R absP polyPrice hullP roy; positivity
    have hQ:= earnA B (α1+2*ε); -- positions
    let G:= GP; let Y:=UP; have hk':Bp=ξ*R:= by unfold R absP; ring
    let bBK:= Bu; have hu:0 ≤ Xp:= mul_nonneg hT (add_nonneg (mul_nonneg hQ (add_nonneg he ha)) (add_nonneg (mul_nonneg hb hK) zero_le_one)); have hg:1 ≤ v^2:= one_le_pow₀ hv; have hz' :X ≤ v^2:=hX.trans hg
    have hG:= etaP (B:=B) (F:=F) (n:=n) (k:=k) (i:=i) (j:=j) hθ hz he ha hc hK
    let Γf:=ξ*v^2
    have hΓ:0 ≤Γf:=mul_nonneg hξ (sq_nonneg _); have hGG: ξ*(GP*v^2)= Γf*G:=by unfold Γf G; ring
    rw [hGG] at hr ⊢; have hτ:0 ≤ θ:=zero_le_one.trans hθ; have he₂:0≤z:=zero_le_one.trans hz; have hW:0 ≤ rP:=by unfold riseP polyPrice; positivity
    let w:=rP*Xp; let kk:=w+θ*(z*w)+z*w; let e:=(hullP B F*C); have hp:0 ≤w:=mul_nonneg hW hu; have hz0:0≤kk:=add_nonneg (add_nonneg hp (mul_nonneg hτ (mul_nonneg he₂ hp))) (mul_nonneg he₂ hp); have hψ:0≤ e:=by unfold e hullP; positivity
    have hRT: b₀ <1:=sub_pos.mp upsilon; have hr':0 ≤ (1-b₀)⁻¹*Xp:= mul_nonneg (inv_pos.mpr upsilon).le hu; have hy:0 ≤ kk*(1+bP):=mul_nonneg hz0 (by linarith only [hb])
    have hGn : (256:ℝ)*e ≤ G ∧ kk*(1+bP) ≤ G ∧ Xp ≤ G∧ (1-b₀)⁻¹*Xp ≤ G:=by
        have hg:G=1+(1-b₀)⁻¹*Xp+kk*(1+bP)+Xp+256*e:=rfl; rw [hg]; constructor; linarith only [hu, hy, hψ, hr']; constructor; linarith only [hu,hy,hψ,hr']; constructor<;>linarith only [hu,hy,hψ,hr']
    have hYZ:0 ≤ Bp:= hk' ▸ mul_nonneg hξ hT -- orientation wrong
    have hY: 0 ≤Y:= add_nonneg (add_nonneg (mul_nonneg hYZ (mul_nonneg hQ he)) (mul_nonneg hYZ (mul_nonneg hQ (mul_nonneg ha (sq_nonneg v))))) (mul_nonneg hYZ (add_nonneg (mul_nonneg hb (mul_nonneg hK hx)) hx))
    have hY' : Y ≤ Γf*Xp:=by
          change Bp*(bBK*Ae) + Bp*(bBK*(At*v^2))+Bp*(bP*(T2*X)+X)≤_; rw [hk'];
          refine (add_le_add (add_le_add ((mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (le_mul_of_one_le_right he hg) hQ) (mul_nonneg hξ hT))) (le_refl _)) (mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hz' hK) hb) hz') (mul_nonneg hξ hT))).trans_eq ?_
          change _= Γf*(R * (bBK*(Ae+At)+(bP*T2+1))); unfold Γf; ring
    have hY₁: Γf*Xp ≤ X*(1-b₀):=by have h := (mul_le_mul_of_nonneg_left hGn.2.2.2 hΓ).trans hr; exact (div_le_iff₀ upsilon).1 (by rwa [div_eq_mul_inv,mul_assoc,mul_comm (pledgeP _ _ _ _ _ _ _ _)] ) -- ambiguity
    have hV:rP*UP ≤ Γf*w:= (mul_le_mul_of_nonneg_left hY' hW).trans_eq (by unfold w; ring); have hBS: w+θ*(z*w)≤ kk:=le_add_of_nonneg_right (mul_nonneg he₂ hp); have hρ: Cp+θ*(z*Cp) ≤ Γf*(w+θ*(z*w)) := by linarith only [hV,mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hV he₂) hτ]
    have hd : w+θ*(z*w) ≤ G:=hBS.trans ((le_mul_of_one_le_right hz0 (by linarith only [hb])).trans hGn.2.1); constructor
    · have hx := (mul_le_mul_of_nonneg_left hGn.1 hΓ).trans (hr.trans hX); have hv':ξ ≤ Γf:=le_mul_of_one_le_right hξ hg; have he:=mul_le_mul_of_nonneg_right hv' hψ; rw [← mul_assoc]; change e *ξ≤_; linarith only [hx,he]
    refine ⟨(show b₀*X+Y ≤X from by linarith only [hY'.trans hY₁]),?_,hY,?_,?_,?_⟩
    · have h : Bp*(Bu*vF) ≤Y:= (le_add_of_nonneg_left (mul_nonneg hYZ (mul_nonneg hQ he))).trans (le_add_of_nonneg_right (mul_nonneg hYZ (add_nonneg (mul_nonneg hb (mul_nonneg hK hx)) hx))); exact h.trans (hY'.trans ((mul_le_mul_of_nonneg_left hGn.2.2.1 hΓ).trans (hr.trans hX))) -- via Xp bound
    · have h1:bP*(w+θ*(z*w)) ≤ G:= (mul_le_mul_of_nonneg_left hBS hb).trans ((mul_le_mul_of_nonneg_right (show bP ≤1+bP from le_add_of_nonneg_left zero_le_one) hz0).trans ((mul_comm ..).le.trans hGn.2.1)); have hg :=mul_le_mul_of_nonneg_left hρ hb; linarith only [hg,(mul_le_mul_of_nonneg_left h1 hΓ).trans (hr.trans hX)]
    · have hm':z*w ≤ kk:=le_add_of_nonneg_left (add_nonneg hp (mul_nonneg hτ (mul_nonneg he₂ hp))); have hy':z*w≤G:=hm'.trans ((le_mul_of_one_le_right hz0 (by linarith only [hb])).trans hGn.2.1); linarith only [mul_le_mul_of_nonneg_left hV he₂,mul_le_mul_of_nonneg_left hy' hΓ]
    linarith only [hρ,mul_le_mul_of_nonneg_left hd hΓ]
end Basal
end YM.MassiveQCD.Sample
#print axioms YM.MassiveQCD.Sample.Basal.healthyP
