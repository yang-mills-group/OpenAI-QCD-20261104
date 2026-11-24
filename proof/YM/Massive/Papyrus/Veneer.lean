import YM.Massive.Papyrus.Ebb
/-! # Polynomial reconstruction of radial jet color coordinates,
conjugate/charge-equivariant and signed-permutation-equivariant.

Panel choice uses the actual verified Wilson-gauge-core Peg, no uniform estimates
here about growth in h/d. Keep all directions till a common S fits.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Papyrus
open Lattice Wilson RG Source Function QCD Source.Drops UV Filter Work.G05 Finset Matrix Labels
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators NNReal Classical
open Scan Paper
variable (H:Hol su)(d h:ℕ)
structure Vine where
   F : Land → Snap su h
   tight : Canvas F
   color (k:Cover→su.El)(x:Land): F (gaugeF k x)= tinted (k 0) h (F x)
   lens : Response d (fun x=>F (trunkJ h H x)) id 0
structure Flag extends Vine H d h where
   stove (x:Land)(s:Signed): F (scene s x)=rot s.ortho⁻¹ h (F x)
   shine (x:Land): F (night x)=recol h (F x)
private lemma flowed {m:ℕ}(u: su.El)(B:GaugePanel su m → Snap su h)(hb: AnalyticAt ℝ B 0)(hp:B ∘ rotates u=ᶠ[𝓝 0]tinted u h ∘ B)(x:GaugePanel su m):
     blockTaylor d B (rotates u x)=tinted u h (blockTaylor d B x):=by
    let M:GaugePanel su m→L[ℝ]GaugePanel su m:= { toFun:= rotates u,map_add':=fun x y=>funext fun j=> map_add (su.adjoint u) (x j) (y j),map_smul':=fun c x=> funext fun j=> map_smul (su.adjoint u) c (x j),cont:=rotates_cont }
    letI:CompleteSpace (Snap su h):= FiniteDimensional.complete ℝ _; exact blockTaylor_equivariant (hb.contDiffAt.of_le (m:=d) le_top) M (tinted u h) hp x
private lemma slotCanvas {m:ℕ}(B:Fin m→ Slot): Canvas (Bid.mapped B (G:=su)):=by
    intro φ; let b := EuclideanSpace.basisFun su.ColorIndex ℝ; let T:= GaugePanel su m; let V (j : Fin m × su.ColorIndex) : GaugePanel su m := Pi.single j.1 (b j.2); let L:= Bid.mapped B (G:=su)
    have ht (p : GaugePanel su m): (∑ j : Fin m × su.ColorIndex, p j.1 j.2 • V j)=p:=by -- adapt G05.Pose
         funext i; rw [← Finset.univ_product_univ, Finset.sum_product, Finset.sum_apply, Finset.sum_eq_single i]
         · simp only [V, Finset.sum_apply, Pi.smul_apply, Pi.single_eq_same]; exact b.sum_repr (p i)
         · intro j _ hj; simp [V, Finset.sum_apply, Pi.smul_apply, Pi.single_eq_of_ne (Ne.symm hj)]
         simp
    have he (x: Land): φ (L x)= ∑ j:Fin m×su.ColorIndex, L x j.1 j.2 • φ (V j):=by
          conv_lhs=> rw [← ht (L x)]
          simp only [map_sum,map_smul]
    change LP (fun x=>φ (L x)); simp_rw [he,Complex.real_smul]; exact series _ _ fun i _=> (current (Work.G06.entryPoly_slot (B i.1) le_rfl i.2)).mul (fixLP _)
private lemma vine_boot {n:ℕ}(B:Fin n→Slot) (f:GaugePanel su n→Snap su h)(hc: AnalyticAt ℝ (bring H h B) 0) (hF: Vision H h B f): Nonempty (Vine H d h):=by
   let F:= blockTaylor d f ∘ Bid.mapped B; refine ⟨⟨F, (slotCanvas B).swing d, fun k u=>?_, ?_⟩⟩
   · unfold F Function.comp; rw [show Bid.mapped B (gaugeF k u)= rotates (k 0) (Bid.mapped B u) from funext fun i=> Work.G01.slot_eval_gauge (B i) u k]; exact flowed d h _ _ hF.1 (hF.2.2.2 (k 0)) _
   let W:= bring H h B; let V:= trunkJ h H; letI:CompleteSpace (Snap su h):= FiniteDimensional.complete ℝ _
   have hz: W 0=0:=funext fun i=> takes_zero ..
   have hf:ContDiffAt ℝ (d:ℕ∞) f 0:=hF.1.contDiffAt.of_le le_top; have H':Response d W W 0:=Response.refl (hc.contDiffAt.of_le le_top)
   refine (H'.transit (v:=blockTaylor d f) (v':=f) (hz.symm ▸ Response.blocked hf)).trans (?_); exact ((Response.eventual (f:=id) contDiffAt_id ((show (fun x=> f (bring H h B x))=ᶠ[𝓝 0] id from hF.2.2.1).symm)).echo)
private lemma baseV : Nonempty (Vine H d h):=by
   have hx: Peg H h:= Work.G02.answer Work.G01.answer su H h; obtain ⟨m,B,hB⟩:= Work.G03.answer su H h hx; obtain ⟨ha,C,h₁,h₂⟩:= Work.G04.answer su H h m B hx hB; obtain ⟨p,hp⟩:= insight ha C h₁ h₂ hx; exact vine_boot H d h B p ha hp
section
variable {E:Type*}[NormedAddCommGroup E][NormedSpace ℝ E]
local notation "σ" => Signed
def MeanF (f:σ→E): E:= ((Fintype.card σ:ℝ))⁻¹ • ∑ i, f i
lemma tone (x:E): MeanF (fun _ : σ=>x)=x:=by unfold MeanF; rw [sum_const, card_univ]; rw [←Nat.cast_smul_eq_nsmul ℝ]; exact inv_smul_smul₀ (by exact_mod_cast Fintype.card_ne_zero) x -- lemma?
lemma noteL {F:Type*}[NormedAddCommGroup F][NormedSpace ℝ F](A:E→L[ℝ]F)(f:σ→E): A (MeanF f)=MeanF fun i=> A (f i):=by simp_rw [MeanF,map_smul,map_sum]
lemma mean_r (f:σ→E)(s:σ): MeanF (fun i=> f (s*i))=MeanF f:=by unfold MeanF; exact congr_arg _ (Equiv.sum_comp (Equiv.mulLeft s) f) -- defeq?
lemma accumulated {A:Type*}[NormedAddCommGroup A][NormedSpace ℝ A](p:σ→A→E)(φ:A→E)(h:∀ i:σ,Response d (p i) φ 0): Response d (fun x=>MeanF (fun i=>p i x)) φ 0:=by
    have hN:= (Response.series univ p (fun _=>φ) 0 (fun i _=>h i)).combo ((Fintype.card Signed:ℝ))⁻¹; change Response d (fun x=> MeanF (fun i=>p i x)) (fun x=> MeanF (fun _=>φ x)) 0 at hN; simp only [tone] at hN; exact hN
end
variable {H d h}
namespace Vine
variable (u: Vine H d h)
abbrev evening (s:Signed)(x:Land):=rot s.ortho h (u.F (scene s x))
lemma evening_response (s:Signed): Response d (fun x=>u.evening s (trunkJ h H x)) (fun x=>x) 0:=by
   let L:=rot s.ortho⁻¹ h
   have hp: L 0=0:=map_zero _
   have hL: Response d (fun x=>L x) (fun x=>L x) 0:= Response.refl L.contDiff.contDiffAt
   have hz:Response d (fun x=> u.F (trunkJ h H (L x))) (fun x=> L x) 0:= hL.transit (v:=fun x=> u.F (trunkJ h H x)) (v':=id) (hp.symm ▸ u.lens)
   have he:= hz.linear (rot s.ortho h); unfold L at he; simp_rw [rot_mul,mul_inv_cancel,rot_unit] at he; unfold evening; simp_rw [← landscape]; exact he
lemma evening_paint (x:Land)(s:Signed)(k:Cover→su.El): u.evening s (gaugeF k x)=tinted (k 0) h (u.evening s x):=by unfold evening; rw [scene_gauge,u.color, Signed.act_zero, rot_paint] -- function β?
lemma evening_sum : Response d (fun i=> MeanF (fun s=> u.evening s (trunkJ h H i))) id 0:=by
   let P(s:Signed)(x:Snap su h):= u.evening s (trunkJ h H x)
   exact accumulated d P id u.evening_response
-- specialized instance
variable {w:Snap su h}
private lemma Cnote (A:Snap su h→L[ℝ]Snap su h)(f:Signed→Snap su h) : A (MeanF f)= MeanF (fun i=> A (f i)):=by unfold MeanF; rw [map_smul,map_sum]
lemma evening_color (k:Cover→su.El)(x:Land): MeanF (fun s=> u.evening s (gaugeF k x))= tinted (k 0) h (MeanF (fun s=> u.evening s x)):=by simp_rw [evening_paint]; exact (Cnote (tinted (k 0) h) (fun s=> u.evening s x)).symm
def crescent : Vine H d h where
    F x:= MeanF fun s=> u.evening s x
    tight:= (Canvas.annual _ _ fun s _=> windup (rot s.ortho h).toLinearMap (u.tight.sees s)).scale _
    color := u.evening_color
    lens:= u.evening_sum
lemma alum (s:Signed)(x: Land): MeanF (fun t=>u.evening t (scene s x)) = rot s.ortho⁻¹ h (MeanF (fun t=>u.evening t x)):=by
    rw [Cnote (rot s.ortho⁻¹ h)]; unfold evening; simp_rw [scene_slide]; symm; rw [← mean_r _ s]; simp only [show ∀ a b:Signed,(a*b).ortho=a.ortho*b.ortho from map_mul Signed.inclusionO]; -- map
    simp_rw [rot_mul, inv_mul_cancel_left]
set_option maxRecDepth 12000 in
set_option maxHeartbeats 600000 in
lemma stove (s:Signed)(x:Land): u.crescent.F (scene s x)= rot s.ortho⁻¹ h (u.crescent.F x):=u.alum s x
def tween (x: Land) : Snap su h:= recol h (u.F (night x))
lemma tween_lens : Response d (fun x=> u.tween (trunkJ h H x)) id 0:=by
    let R:= recol h; let v:=fun x=> R x; let J:=trunkJ h H
    have hR:Response d v v 0:=Response.refl R.contDiff.contDiffAt
    have hz: v 0=0:=map_zero _; have hf: Response d (fun i=> u.F (J (R i))) v 0:= hR.transit (v:=u.F ∘ J) (v':=id) (hz.symm ▸ u.lens)
    have hj:= hf.linear R; rw [show (fun i=> R (v i))=id from funext fun x=> recol_back x] at hj
    unfold tween; simp_rw [←Scan.spectrum]; exact hj
abbrev spreadT (x:Land):Snap su h:= (1/2:ℝ) • (u.F x+ u.tween x)
lemma spread_r : Response d (fun x=> u.spreadT (trunkJ h H x)) id 0:=by
    have hf:= Response.combo (1/2:ℝ) (u.lens.plus u.tween_lens); rw [show (fun x:Snap su h=> (1/2:ℝ) • (id x + id x))=id from funext fun x=>by simp only [id_eq,← two_smul ℝ,smul_smul,div_mul_cancel₀ _ (two_ne_zero' ℝ),one_smul]] at hf; exact hf
lemma spread_c : Canvas u.spreadT:=by
    have ht: Canvas u.tween:=windup (recol h).toLinearMap u.tight.odd
    exact (u.tight.add ht).scale (1/2:ℝ)
lemma spread_g (k:Cover→su.El)(x: Land): u.spreadT (gaugeF k x)=tinted (k 0) h (u.spreadT x):=by unfold spreadT tween; rw [night_gauge,u.color,u.color,Function.comp_apply,recol_paint, UV.conjugate_inv, map_smul,map_add]
lemma spread_s (s:Signed)(x: Land): u.crescent.spreadT (scene s x)=rot s.ortho⁻¹ h (u.crescent.spreadT x):=by unfold spreadT tween; rw [night_scene,u.stove,u.stove, map_smul,map_add,recol_rot]
lemma spread_w (x: Land): u.spreadT (night x)=recol h (u.spreadT x):=by unfold spreadT tween; rw [show night (night x)=x from congr_fun night_double x,map_smul,map_add,recol_back,add_comm]
include u
theorem filterD : Nonempty (Flag H d h):=by
   let V:=u.crescent; exact ⟨{F:=V.spreadT,tight:=V.spread_c,color:=V.spread_g,lens:=V.spread_r,shine:=V.spread_w,stove:=fun x s=>u.spread_s s x}⟩
end Vine
theorem photo (H:Hol su)(d h:ℕ): Nonempty (Flag H d h):=(Classical.choice (baseV H d h)).filterD
end YM.Massive.Papyrus
#print axioms YM.Massive.Papyrus.photo
