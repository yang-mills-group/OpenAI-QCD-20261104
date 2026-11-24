import YM.QCD.Cedar.Sprig
import YM.QCD.Step.Rooted

/-!
# global Coercivity of the free-reference extensions under one-step high Gaussian
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Pine
open Lat Cost Lattice Wilson Function Finset Flume
open Laurent Bloch YM.Next.Free Metric Kit Free
open scoped Matrix.Norms.L2Operator Topology BigOperators Matrix Kronecker
variable {c f n : Side} {j k : ℕ} (P : Plan j)

def vaultF (F : Flight j k) (h : f.val=c.val*F.L.val) (t : Site f) (U : Grid f):= wood P t F.wing U+(tied F h t U)ᴴ*tied F h t U
variable (F : Flight j k) (h : f.val=c.val*F.L.val) (t : Site f) (U : Grid f)
lemma gammaQ (a : Axis) : ‖onSpin n (gamma a)‖ ≤ 1:=by
  have he := Matrix.l2_opNorm_conjTranspose_mul_self (onSpin n (gamma a)); rw [← Matrix.star_eq_conjTranspose, on_spin_star,gamma_star,on_spin_mul,gamma_sq,on_spin_one,oneNorm] at he; nlinarith
lemma grade_wood : ∃ C:ℝ,0<C ∧ ∀ v : Train j, ∀ (f : Side) (t : Site f) (U : Grid f), ‖wood P t v U‖ ≤ C:=by
  obtain ⟨η,C,he,hc,H⟩:=alpha_cash P.good (fun i : Train j=>i)
  obtain ⟨σ,D,hp,hd,G⟩:= P.herm_paid (fun i:Train j×Axis=> i.1) (fun i=>i.2)
  let X:=4*P.μ+(D*2)^2+C
  have hX: 0<X:=by dsimp[X]; have ht:=P.price; positivity
  refine ⟨4*X,by positivity,fun v f t U=>?_⟩
  unfold wood; refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun a _=>?_).trans (le_of_eq (by simp [Axis] : ∑ _ : Axis,X=4*X))) -- parentheses
  have hf : ‖arcL t U a‖≤2:= by unfold arcL; exact (norm_sub_le ..).trans (by rw [oneNorm]; linarith [rotation_price (shift_u t U a)])
  have hr : ‖deck t U (P.Herm v a)‖≤D:=by simpa only [mul_one] using valueD (P.Herm v a) (G (v,a)) hp.le t U
  have hy : ‖deck t U (alphaT v a)‖≤C:=valueD _ (H _ _) he.le t U
  have hm (Z : Sheet f) : ‖leaves Z‖=‖Z‖^2:=by rw [leaves,Matrix.star_eq_conjTranspose, Matrix.l2_opNorm_conjTranspose_mul_self,pow_two]
  let W := deck t U (P.Herm v a)
  let B := arcL t U a
  have ha (A : Sheet f) (hA : ‖A‖≤ 2): ‖leaves (W*A)‖≤(D*2)^2:= by rw [hm]; exact pow_le_pow_left₀ (norm_nonneg _) ((norm_mul_le ..).trans (mul_le_mul hr hA (norm_nonneg _) hd.le)) _
  have hv (Y : Sheet f) : ‖skewL Y‖≤ ‖Y‖:= by unfold skewL; rw [norm_smul,norm_inv]; apply (mul_le_mul_of_nonneg_left (norm_sub_le ..) (by positivity)).trans; rw [norm_star]; norm_num; ring_nf; exact le_rfl
  have hw : ‖walls P t v U a‖ ≤ 4*P.μ+(D*2)^2 := by
    unfold walls half; dsimp only; refine (norm_add_le ..).trans (add_le_add ?_ ?_)
    · rw [norm_smul, Complex.norm_real,Real.norm_of_nonneg P.price.le, hm]; exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hf 2) P.price.le).trans (le_of_eq (by ring))
    rw [norm_smul,norm_inv]
    refine (mul_le_mul_of_nonneg_left ((norm_add_le ..).trans (add_le_add (ha B hf) (ha _ (by rw [norm_star]; exact hf)))) (by positivity)).trans (le_of_eq ?_); norm_num; ring
  refine (norm_add_le ..).trans (add_le_add hw ((hv _).trans ?_)); unfold vein; exact (norm_mul_le ..).trans ((mul_le_mul (gammaQ a) hy (norm_nonneg _) zero_le_one).trans (by rw [one_mul]))
lemma mass_pos (L : Side) : 0 < massL L := mul_pos (slope_pos _) (pow_pos (side_pos _) _)
lemma towerB : ‖tied F h t U‖≤massL F.L:=by
  let r:=sliceL F h
  have he (o:Lattice.Order) : ‖lineF F h t U o‖≤1:=by
    unfold lineF; refine (norm_sum_le _ _).trans ((sum_le_sum ?_).trans (le_of_eq F.patch.weight_sum))
    intro a _; rw [norm_smul,Complex.norm_real,Real.norm_of_nonneg (F.patch.weight_nonneg _)]; apply mul_le_of_le_one_right (F.patch.weight_nonneg _)
    exact (Matrix.l2_opNorm_mul _ _).trans ((mul_le_mul (price_scoop _).le (rotation_price (circle t U _)) (norm_nonneg _) zero_le_one).trans (by rw [one_mul])) --
  unfold tied; rw [norm_smul,norm_smul,norm_inv,Complex.norm_natCast,Complex.norm_real,Real.norm_of_nonneg (mass_pos _).le]
  refine mul_le_of_le_one_right (mass_pos _).le ((mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (sum_le_sum fun i _=> he i)) (by positivity)).trans (le_of_eq ?_))
  rw [sum_const,card_univ,nsmul_eq_mul,mul_one,inv_mul_cancel₀ Kit.poll_pos.ne']
lemma overall : ∃ C:ℝ,0<C ∧ ∀ F:Flight j k, ∀ (c f: Side) (h : f.val=c.val*F.L.val) t U, ‖vaultF P F h t U‖ ≤ C+massL F.L^2 := by
  obtain ⟨C,hc,H⟩:=grade_wood P; refine ⟨C,hc,fun F c f h t U=>?_⟩; unfold vaultF; refine (norm_add_le ..).trans (add_le_add (H ..) ((Matrix.l2_opNorm_conjTranspose_mul_self _).le.trans ?_)); rw [← pow_two]; exact pow_le_pow_left₀ (norm_nonneg _) (towerB ..) _

def arctic (L:Side) (j:ℕ):=4*((j+3)*L.val)
lemma stems (a : F.patch.Points) (o:Lattice.Order): (route 0 a.val o).length ≤ arctic F.L j:=by
  have hx:= box_test.mp a.property
  have he (l : List Axis) : (axisRoute 0 a.val l).length≤ l.length*F.patch.radius:=by
    induction l with
    | nil=> simp [axisRoute]
    | cons i l ih=>
      rw [show axisRoute 0 a.val (i::l)=straight i (a.val i-0)++axisRoute 0 a.val l from rfl,List.length_append,List.length_cons]
      simp only [straight,List.length_replicate,sub_zero]; have h1:=hx.1 i; have h2:=hx.2 i; rw [Nat.add_mul]; omega
  have hp:=he (allAxes o); simp only [allAxes,List.length_map,List.length_finRange] at hp; exact hp
lemma sticks (x : Vec (Row f)) : ‖lead (scoop (sliceL F h)) x‖≤ (massL F.L)⁻¹*‖lead (tied F h t U) x‖ + (arctic F.L j)*estate t U x := by
  let L:=F.L
  let B:=scoop (sliceL F h)
  let E:= (arctic F.L j)*estate t U x; have hE : 0≤E:=mul_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _)
  have ht (w:Walk) (hw:w.length≤ arctic F.L j): ‖lead (B*routeM t U w) x-lead B x‖ ≤ E := by
    rw [lead_act,← map_sub,lead_op]; exact (leanBound _ _).trans (by rw [price_scoop,one_mul]; exact (walk_budget ..).trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hw) (Real.sqrt_nonneg _)))
  have hg (o:Lattice.Order) : ‖lead (lineF F h t U o) x-lead B x‖≤E:=by
    have hh : ∑ a:F.patch.Points,(F.patch.weight a:ℂ) • lead B x=lead B x:=by rw [← sum_smul,← Complex.ofReal_sum,F.patch.weight_sum,Complex.ofReal_one,one_smul]
    nth_rw 1 [← hh]; unfold lineF; simp only [map_sum,_root_.sum_apply,map_smul,ContinuousLinearMap.smul_apply,← sum_sub_distrib,← smul_sub]
    refine (norm_sum_le _ _).trans ((sum_le_sum (g:=fun a=>F.patch.weight a * E) ?_).trans (le_of_eq (by rw [← sum_mul,F.patch.weight_sum,one_mul])))
    intro i _; rw [norm_smul,Complex.norm_real,Real.norm_of_nonneg (F.patch.weight_nonneg _)]
    exact mul_le_mul_of_nonneg_left (ht _ (stems ..)) (F.patch.weight_nonneg _)
  let A := ((votes:ℂ)⁻¹) •∑ o,lineF F h t U o
  have he : ‖lead A x -lead B x‖ ≤ E := by
    have hh : (votes:ℂ)⁻¹ • ∑ _ : Lattice.Order, lead B x=lead B x:= by rw [sum_const,card_univ, ← Nat.cast_smul_eq_nsmul ℂ,smul_smul,inv_mul_cancel₀ votes_ne,one_smul]
    rw [← hh]; unfold A; simp only [map_smul,map_sum,_root_.sum_apply,ContinuousLinearMap.smul_apply,← smul_sub, ← sum_sub_distrib]; rw [norm_smul,norm_inv,Complex.norm_natCast]
    refine (mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (sum_le_sum fun i _=> hg i)) (by positivity)).trans (le_of_eq ?_)
    rw [sum_const,card_univ,nsmul_eq_mul,← mul_assoc,inv_mul_cancel₀ poll_pos.ne',one_mul]
  change ‖lead B x‖ ≤ (massL L)⁻¹ * ‖lead ((massL L:ℂ) • A) x‖+E
  rw [map_smul, ContinuousLinearMap.smul_apply,norm_smul, Complex.norm_real,Real.norm_of_nonneg (mass_pos _).le, ← mul_assoc, inv_mul_cancel₀ (mass_pos _).ne',one_mul]; linarith [norm_sub_norm_le (lead B x) (lead A x),norm_sub_rev (lead A x) (lead B x)]
def item (L : Side) : ℝ:= (L.val:ℝ)^2 * (massL L)⁻¹
def altar (L : Side) (j : ℕ):ℝ:=(L.val:ℝ)^2*((arctic L j)+reach L)
lemma forage (x: Vec (Row f)): ‖x‖≤ item F.L * ‖lead (tied F h t U) x‖ + altar F.L j * estate t U x:=by
  let r:=sliceL F h
  let M:=‖lead (tied F h t U) x‖
  let G:=estate t U x
  let A:ℝ:=(massL F.L)⁻¹*M
  let B:ℝ:=((arctic F.L j:ℝ)+reach F.L)*G
  have hk (i:Site r.count):‖lead (stripe r t U 1 i) x‖≤ A+B:= by
    have hm := mismatch r t U 1 i x
    rw [map_sub,ContinuousLinearMap.sub_apply] at hm
    have hh:‖lead (scoop r) x‖≤ A+↑(arctic F.L j)*G := sticks ..
    have he:= (norm_sub_norm_le ..).trans hm
    unfold B; change _ ≤ _ at he -- inspect
    change _ ≤ (reach F.L:ℝ)*G at he; linarith
  have hb:0≤A+B:= add_nonneg (by unfold A M; have h:= mass_pos F.L; positivity) (mul_nonneg (by positivity) (Real.sqrt_nonneg _))
  calc
    _ ≤ (F.L.val:ℝ)^2*(A+B):=by
      rw [← sq_le_sq₀ (by positivity) (mul_nonneg (by positivity) hb),← concurs r t U 1]; refine (sum_le_sum fun i _=> pow_le_pow_left₀ (norm_nonneg _) (hk i) _).trans (le_of_eq ?_); rw [sum_const,card_univ,nsmul_eq_mul,site_card]; push_cast; dsimp [r]; ring
    _ = _:=by unfold item altar A B M G; push_cast; ring

def stamp (L : Side):= (2*item L^2 +2*altar L j^2 /P.μ + 1)
def minGap (L : Side):= (stamp P L)⁻¹
lemma healthy (L) : 0<stamp P L:=by unfold stamp; have h:=P.price; positivity
lemma sealPos (L) : 0<minGap P L:=inv_pos.mpr (healthy P L)
lemma lease : Floor (minGap P F.L) (vaultF P F h t U):=by
  intro x
  let L:= F.L
  let E:= stamp P L
  let G:= estate t U x
  let Q:= ‖lead (tied F h t U) x‖
  have he : ‖x‖^2 ≤ (item L *Q+ altar L j*G)^2:=pow_le_pow_left₀ (norm_nonneg _) (forage ..) _
  have hi:=P.price
  have hp:0<E:=healthy P _
  have hh:2*item L ^2≤E:=by
    dsimp only [E,stamp]; have h : 0≤2* altar L j^2/P.μ:=by positivity
    linarith
  have hq : 2*altar L j^2 ≤ P.μ * E := by unfold E stamp; field_simp; nlinarith only [hi,sq_nonneg (item L),mul_nonneg hi.le (sq_nonneg (item L))] -- inspect
  rw [vaultF, Cost.add_form, cross_square]; refine le_trans ?_ (add_le_add_left (engrave P _ F.wing U x) _) -- check
  change E⁻¹ * ‖x‖^2 ≤ P.μ*G^2+Q^2; rw [inv_mul_eq_div, div_le_iff₀ hp]; nlinarith only [he,mul_le_mul_of_nonneg_right hh (sq_nonneg Q),mul_le_mul_of_nonneg_right hq (sq_nonneg G),sq_nonneg (item L*Q-altar L j*G)]
end YM.QCD.Pine
