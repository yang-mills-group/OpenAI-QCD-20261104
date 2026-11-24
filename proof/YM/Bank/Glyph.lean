import YM.Bank.Osc
set_option autoImplicit false
noncomputable section
namespace YM.Bank.Glyph
open Wilson Gauge Function Lattice Laurent Bloch Metric RG Precision Filter Finset Next.Free
open Learn Wale Osc Pilot
open Matrix Exterior
open scoped Topology Matrix Matrix.Norms.L2Operator ComplexConjugate BigOperators
local notation "θ"=> TypeFace 2
local notation "δ"=> TypeFace 1
variable {a b t s r:ℝ}{p q:Momentum}{c:Side}{P:Row θ θ}{n m l:Type}

section matrices
variable [Fintype n][Fintype m][Fintype l][DecidableEq n][DecidableEq m][DecidableEq l]
def listenD (i:n)(j:m): Matrix n m ℂ →L[ℂ] ℂ:= LinearMap.toContinuousLinearMap
   {toFun:=fun x=> x i j,map_add':=fun _ _=>rfl,map_smul':=fun _ _=>rfl}
lemma mosaic {A:Momentum→Matrix n m ℂ}(h:∀ i j, DifferentiableAt ℂ (fun p=> A p i j) q): DifferentiableAt ℂ A q := (Merchant.mapping n m).differentiableAt.comp (f:=fun p=>Matrix.of.symm (A p)) q (differentiableAt_pi.mpr fun i=> differentiableAt_pi.mpr (h i))
lemma mat_prod {A:Momentum→Matrix n m ℂ}{B:Momentum→Matrix m l ℂ}(h:DifferentiableAt ℂ A q)(g:DifferentiableAt ℂ B q): DifferentiableAt ℂ (fun p=> A p* B p) q:=by
   refine mosaic (fun i j=>?_); simp_rw [Matrix.mul_apply]; apply DifferentiableAt.fun_sum; intro k _; exact ((listenD i k).differentiableAt.comp q h).mul ((listenD k j).differentiableAt.comp q g)
end matrices
lemma mirrors (k:ℕ){p:Momentum}: DifferentiableAt ℂ (signal 1 k) p ∧ DifferentiableAt ℂ (mirage 1 k) p:=by
    have H q: DifferentiableAt ℂ (signal 1 k) q:=by unfold signal tripQ wedge chip; fun_prop
    exact ⟨H _, mosaic fun i j=> (listenD j i).differentiableAt.comp p ((H (-p)).comp p (show DifferentiableAt ℂ (fun v:Momentum=>-v) p from differentiableAt_id.neg))⟩ -- inspect
lemma hol_sig (hp:P.strip r b)(hr:0<r)(hq:q∈cube (r/2)): DifferentiableAt ℂ (gaugeR P) q := (mat_prod (mat_prod (mirrors _).2 (hol_d hp hr hq)) (mirrors _).1).add (mat_prod (mirrors _).1 (mirrors _).2)
def district (b:ℝ) := Merchant.relay 1*‖Merchant.ℳ‖*b*Merchant.relay 1 + Merchant.relay 0^2
lemma district_pos (hb:0≤b): 0≤district b := add_nonneg (Merchant.bankT_pos b hb) (sq_nonneg _)
-- transmirage norm
lemma mir_cost (k:ℕ)(hv:q∈cube zone): ‖mirage 1 k q‖ ≤ Merchant.relay k*‖q‖:=by -- replicate helper
    have he (p) (k:ℕ): mirage 1 k p=(signal 1 k (star p))ᴴ:=by
       unfold mirage signal; rw [wedge_adj]; unfold tripQ; congr! 3 with i
       -- maybe
       simp [flip_chip]
    have hx (k:ℕ) : ‖mirage 1 k q‖ ≤ Merchant.relay k*‖q‖:=by
      rw [he, l2_opNorm_conjTranspose]; have hh: star q∈cube zone:=by
        constructor
        · intro i; simpa using hv.1 i
        intro i; simpa using hv.2 i
      have hu:=Merchant.lay_cost hh k; rw [norm_star] at hu; exact hu
    exact hx k
lemma hol_size (hp:P.strip r b)(hr:0<r)(hb:0≤b)(hq:q∈cube (r/2))(hv:q∈cube zone): ‖gaugeR P q‖≤ district b*‖q‖^2:=by
    let V:=signal 1 1 q; let A:=mirage 1 1 q; let X:= P.read q
    let W:=signal 1 0 q; let B:=mirage 1 0 q
    have hx (k:ℕ) := mir_cost k hv
    have hl : ‖X‖ ≤ ‖Merchant.ℳ‖*b:= holM hp hr hb hq
    have hA := (l2_opNorm_mul A X).trans (mul_le_mul (hx 1) hl (norm_nonneg _) ((norm_nonneg _).trans (hx 1)))
    have hB := Merchant.lay_cost hv 0
    have hK:= (l2_opNorm_mul (A*X) V).trans (mul_le_mul hA (Merchant.lay_cost hv 1) (norm_nonneg _) ((norm_nonneg _).trans hA))
    have hW:= (l2_opNorm_mul W B).trans (mul_le_mul hB (hx 0) (norm_nonneg _) ((norm_nonneg _).trans hB))
    exact (norm_add_le ..).trans ((add_le_add hK hW).trans_eq (by unfold district; ring))
section
open QCD.Cost
lemma ford {w d:ℝ} {X Y: Matrix δ δ ℂ}(h:‖X-Y‖≤d)(hp: QCD.Cost.Floor w Y): QCD.Cost.Floor (w-d) X:=by
    intro p
    have he : |QCD.Cost.form (X-Y) p| ≤ d*‖p‖^2:=by unfold QCD.Cost.form; refine (Complex.abs_re_le_norm _).trans ((norm_inner_le_norm p _).trans ((mul_le_mul_of_nonneg_left ((leanBound _ _).trans (mul_le_mul_of_nonneg_right h (norm_nonneg _))) (norm_nonneg p)).trans_eq ?_)); ring -- confusion
    have hg : QCD.Cost.form X p=QCD.Cost.form (X-Y) p + QCD.Cost.form Y p:=by rw [←add_form,sub_add_cancel]
    rw [hg]; linarith only [(abs_le.mp he).1, hp p]
end
lemma carpet (a b r:ℝ)(ha:0<a)(hb:0≤b)(hr:0<r) : ∃ s C,0<s ∧ s≤1 ∧ 0≤ C∧∀ {c:Side}(P:Bed),P.metric.strip r b→Numeric (P.metric.acts c) a b→∀ p: Site c,mon p≠0→ ∀ q∈collar (mon p) s, q∈cube zone ∧ DifferentiableAt ℂ (skyF P) q∧ ‖skyF P q‖≤ C/‖mon p‖:=by
    obtain ⟨ρ,hρ,h₁,H⟩:= cup_z r hr
    let d:=4*district b+1; have hd:0<d:=by unfold d; linarith [district_pos hb]
    let e:= lum a/2; have he:0<e:=half_pos (luminous ha)
    let s:=min (ρ/2) (ρ/(2*d)*e)
    have hs: 0<s:=lt_min (half_pos hρ) (by positivity); have ht:s≤ρ/2:=min_le_left ..; let F:= (2*Merchant.relay 1)^2/e; let C:=F*Real.pi; have hw: 0≤F:=by unfold F; positivity
    refine ⟨s,C,hs,by linarith,by unfold C; positivity,fun {c} P hp hg p h v hv=>?_⟩
    let u:= mon p; let t:= ‖u‖; have hu: 0<t:= norm_pos_iff.mpr h
    have hx : v∈ball u (ρ*t/2):= ball_subset_ball (le_trans (mul_le_mul_of_nonneg_right ht hu.le) (le_of_eq (by unfold t u; ring : ρ/2*‖mon p‖= _))) hv
    have hi:= H _ (mon_mem c p); have hk: ball u (ρ*t/2) ⊆ collar (mon p) ρ:= ball_subset_ball (half_le_self (by change 0≤ρ*t; positivity))
    have hl:= hi _ (hk hx)
    let X := gaugeR P.metric; have hQ : ∀ q∈ ball u (ρ*t),DifferentiableAt ℂ X q:=fun q hq=> hol_sig hp hr (hi _ hq).1
    have hz : ‖X v-X u‖ ≤ d*t^2/(ρ*t/2)*‖v-u‖ :=by
       refine QCD.Run.lastwig X (by positivity) hQ (fun q hq=>?_) hx
       have he:= hi _ hq; apply (hol_size hp hr hb he.1 he.2.1).trans;
       exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) he.2.2 _) (district_pos hb)).trans (by unfold d t u; nlinarith [sq_nonneg ‖mon p‖])
    have hz' : ‖X v-X u‖≤e*t^2:=by
       have hw: ‖v-u‖≤s*t:=by rw [← dist_eq_norm]; exact (mem_ball.mp hv).le
       have ht1:s ≤ ρ/(2*d)*e:=min_le_right ..
       exact hz.trans ((mul_le_mul_of_nonneg_left (hw.trans (mul_le_mul_of_nonneg_right ht1 hu.le)) (by positivity)).trans_eq (by field_simp))
    have hX: QCD.Cost.Floor (e*t^2) (X v):=by
       convert ford hz' (funds_b P.metric hg ha p (Row.rights _ _ hp hr.le)) using 1; unfold e t u; ring
    have h0: 0 < e*t^2:= mul_pos he (pow_pos hu _)
    let A:=signal 1 1 v; let B:= spaceK P.metric v; let Y:=mirage 1 1 v; let D:=Merchant.relay 1*(2*t)
    have hB : ‖B‖ ≤ (e*t^2)⁻¹:=hX.reciprocal h0
    have hT: ‖v‖≤2*t:= hl.2.2
    have hA : ‖A‖ ≤ D:= (Merchant.lay_cost hl.2.1 1).trans (mul_le_mul_of_nonneg_left hT (Merchant.relay_pos _))
    have hG:= mul_le_mul hA hB (norm_nonneg _) ((norm_nonneg _).trans hA)
    refine ⟨hl.2.1,mat_prod (mat_prod (mirrors _).1 ?_) (mirrors _).2,?_⟩
    · have hp: DifferentiableAt ℂ (fun i=> Ring.inverse (X i)) v:=by
          apply DifferentiableAt.comp (g:=Ring.inverse) (f:=X) (x:=v) _ (hQ _ (hk hx)); obtain ⟨i,hℓ⟩:=(X v).isUnit_iff_isUnit_det.mpr (hX.unit h0); rw [←hℓ]; exact (hasFDerivAt_ringInverse _).differentiableAt
      convert hp using 1; ext1 q; exact Matrix.nonsing_inv_eq_ringInverse _
    have hy :‖Y‖ ≤ D:= (mir_cost 1 hl.2.1).trans (mul_le_mul_of_nonneg_left hT (Merchant.relay_pos _))
    refine (l2_opNorm_mul (A*B) Y).trans (le_trans (mul_le_mul ((l2_opNorm_mul A B).trans hG) hy (norm_nonneg _) ((by positivity : 0≤ ‖A‖ * ‖B‖).trans hG)) (le_trans (b:=F) (le_of_eq ?_) ((le_div_iff₀ hu).mpr (mul_le_mul_of_nonneg_left (QCD.Pearl.cap_base (mon_mem c p)) hw))))
    unfold F D; field_simp
end YM.Bank.Glyph
#print axioms YM.Bank.Glyph.carpet
