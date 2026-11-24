import YM.Massive.Mass.Kernels
import YM.QCD.Finch.Offer
/-!
# Compare to actual jet mass signal
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Reading
open QCD QCD.Lat Lattice Wilson Function QCD.Grass QCD.Stew QCD.Globe QCD.Globe.HalfMass
open QCD.Flume QCD.Cove QCD.Finch QCD.Reggae -- Phase namespace?
open High.PrismT Project YM.Next.Free
open Filter Finset
open scoped Topology ContDiff Classical Matrix BigOperators Matrix.Norms.L2Operator
variable {c : Side} {A ε : ℝ} {j k N m : ℕ} (X : Sheet c)

lemma sign_flag : (center X corep chad chad).re = flagW X:=by
  have he : center X corep chad chad=QCD.Free.peel X (0,chad) (0,chad):=by
    unfold center cashRow; simp only [Matrix.smul_apply, Matrix.sum_apply];
    have h : ∑ i: Site c,∑ j:Site c, corep i j • QCD.Run.cell X i j chad chad=stow X:= (Fintype.sum_prod_type (fun v: Site c × Site c=> Finch.corep v.1 v.2 • QCD.Run.cell X v.1 v.2 chad chad)).symm -- arg
    rw [h,pStow,smul_eq_mul,inv_mul_cancel_left₀]; exact_mod_cast Fintype.card_ne_zero (α:=Site c)
  exact congr_arg Complex.re he
lemma sign_toll : (center X Stew.shine chad chad).re= Project.unitF false c X:=by
  let A:ℕ:= Fintype.card (Site c); let B:=(∑ i:Site c,∑ j:Site c,shine i j • QCD.Run.cell X i j); have hp : center X shine=(A:ℂ)⁻¹ • B:=rfl
  have ht : ∀ i j,Project.stone c false i j=shine i j:= fun _ _=> by simp [Project.stone]
  have hx : Project.μDir c false X ((0,0):Pinor) (0,0)= B chad chad:=by
    change (∑ i,∑ j,Project.stone c false i j • gold (QCD.Run.cell X i j)) _ _= _; unfold B; simp only [Matrix.sum_apply, Matrix.smul_apply,ht]; rfl
  rw [hp]; change ((A:ℂ)⁻¹ * B chad chad).re=(A:ℝ)⁻¹ * ((Project.μDir c false X (0,0) (0,0)).re)
  rw [hx]; simp -- complex

lemma ray (x:Site c) : Run.plane x=star (Finch.violet x):=by
  unfold Run.plane Finch.violet QCD.Flume.rep tuning QCD.Free.menu QCD.Free.fixed QCD.Free.spacer Laurent.mode;
  -- inspect scalar rewrites
  simp [← Complex.exp_conj, Pi.smul_apply, lift]
  simp only [ZMod.cast_eq_val,map_natCast,Complex.ofReal_natCast]; rw [mul_sum]; apply congr_arg; ring_nf

lemma close1 : Close (Stew.shine (c:=c)) 0:=by intro i j; simp
noncomputable abbrev budget := 2*4*Real.pi
lemma closeG : Close (c:=c) Finch.corep budget:=by intro i j; simpa [amount,separation_comm i j] using crumple i i j
lemma closeRe : Close (c:=c) (fun i j=>star (Run.plane i)*Run.plane j) budget:=by
   intro i j; rw [show star (Run.plane i)*Run.plane j-shine i j= star (corep i j-shine i j) from ?_,norm_star];
   · exact closeG i j
   rw [ray,ray,corep,star_sub,star_mul',realSS]

lemma read_toll (hm:1≤ m) (hp:Beam X m A) (hx:Tempo X):
    amount c * |unitF false c X - Globe.mass X| ≤ 20*A:=by
  rw [← sign_toll]; have hu:= coat X _ hm (show 0 ≤ (0:ℝ) from le_rfl) close1 hp hx chad; rw [zero_add] at hu
  apply le_trans _ hu; apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _); exact Complex.abs_re_le_norm (center X Stew.shine chad chad - mass X)
lemma read_flag (hm:1≤ m) (hp:Beam X m A) (hx:Tempo X) :
    amount c * |flagW X - Globe.mass X| ≤ (budget+20)*A:=by
  rw [← sign_flag]; have hu:= coat X Finch.corep hm (by unfold budget; positivity : 0 ≤ budget) closeG hp hx chad
  apply le_trans _ hu; apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _); exact Complex.abs_re_le_norm (center X corep chad chad - mass X)

lemma large : Tendsto amount atTop atTop:=by
  let f : Side → ℕ:= fun x=> x.val; refine tendsto_natCast_atTop_atTop.comp (tendsto_atTop.2 (fun n=>?_));
  filter_upwards [eventually_ge_atTop (⟨n+1,Nat.zero_lt_succ _⟩:Side)] with c he; change _ ≤ f c; change n+1 ≤ f c at he; omega

-- planner estimates, arbitrary shape admissible Plan
lemma sunny_toll (P:Plan j) (hj:4 ≤ j) (he:0< ε) : ∀ᶠ c:Side in atTop,∀ (V:Train j),|unitF false c (sunny P V c)|≤ ε:=by
   let F(i:Side):= (i.val:ℝ); obtain ⟨M,hM,H⟩:= bounces P 2; let D:=20*M+(budget+20)*M
   filter_upwards [earnings P (half_pos he) hj (k:=4) le_rfl 3,large.eventually_ge_atTop (D/(ε/2))] with c hp hc V
   let B:=sunny P V c; have h := hp.1 V
   have hC: F c * |unitF false c B - flagW B| ≤ D:=by
         let q:=Globe.mass B
         have h : |unitF false c B-flagW B| ≤ |unitF false c B-q|+|flagW B-q|:=by rw [← abs_sub_comm q (flagW B)]; apply abs_sub_le
         apply (mul_le_mul_of_nonneg_left h (by unfold F; positivity)).trans; rw [mul_add]; exact add_le_add (read_toll _ (by omega) (H V c) (savior P V)) (read_flag _ (by omega) (H V c) (savior P V))
   have hi : 0 < F c:= by unfold F; positivity
   have hc : D≤F c*(ε/2):= (div_le_iff₀ (half_pos he)).1 hc; have hv:= le_of_mul_le_mul_left (hC.trans hc) hi
   change |unitF false c B|≤_; change |flagW B|≤ ε/2 at h; obtain ⟨h1,h2⟩ := abs_le.mp h; obtain ⟨h3,h4⟩ := abs_le.mp hv; apply abs_le.mpr; constructor<;> linarith only [h1,h2,h3,h4]

-- terminal row. explicit factor of reference spacing; scheme using AP(- reversed).
def planeProbe (A : Density c N)(i:Flavor N): ℂ:=
  (∑ x:Site c,∑ y:Site c,∑ v:Lat.Fiber, star (Run.plane x)* Run.negQuadratic A ((x,v),i) ((y,v),i) * Run.plane y) / ((Fintype.card (Site c):ℂ) * (Fintype.card Lat.Fiber:ℕ))

lemma true_plane (X:Grid c → EvenA c N) (b:Flavor N) (p:Flavor N) (h:Patron.Fit (X 1)) :
    planeProbe (light _ ∘ X) b= (↑(Fintype.card Lat.Fiber):ℂ)⁻¹ * ∑ i,center (fumes p (X 1)) (fun i j=>star (Run.plane i)*Run.plane j) i i:=by
   simp_rw [planeProbe,quadr b X, (indistinguishable b _ h p).2];
   let A (x y: Site c)(v:Lat.Fiber):= (star (Run.plane x)*Run.plane y)* (fumes p (X 1) (x,v) (y,v));
   have hh : ∑ x,∑ y,∑ v:Lat.Fiber, star (Run.plane x) * fumes p (X 1) (x,v) (y,v)* Run.plane y= ∑ v,∑ x:Site c,∑ y:Site c,A x y v:=by
      rw [sum_comm (f:=fun v x=>∑ y,A x y v)]; apply sum_congr rfl; intro x _; rw [sum_comm (f:=fun v y=>A x y v)]; unfold A; congr 1; ext1 y; apply sum_congr rfl; intro i _; ring -- check
   rw [hh]; simp only [div_eq_mul_inv,mul_inv_rev,center, cashRow, Matrix.smul_apply, Matrix.sum_apply,smul_eq_mul]; rw [← mul_sum]; let q:=∑ i, ∑ x, ∑ y:Site c,A x y i; change q*((↑(_:ℕ):ℂ)⁻¹ * (↑(_:ℕ):ℂ)⁻¹) = _*(_*q); ring


theorem cost_plane (X : Grid c → EvenA c N) (b b' : Flavor N) (h : Patron.Fit (X 1)) (K : Sheet c)(he : K=fumes b' (X 1))
    (hT : Tempo K)(hp: Beam K m A) (hv:1 ≤ m) : amount c * ‖planeProbe (light _ ∘ X) b - (Project.unitF false c K:ℂ)‖ ≤ (budget+40)*A:=by
  let u:= unitF false c K; let k := Fintype.card Lat.Fiber; let w : Site c→Site c→ℂ :=fun i j=> star (Run.plane i)*Run.plane j
  have hQ :0 ≤ budget:=by unfold budget; positivity
  have hc:0≤amount c:=Nat.cast_nonneg _
  have hl (i): amount c*‖center K w i i-(u:ℂ)‖ ≤ (budget+40)*A:=by
        let z:ℂ:= mass K; rw [show _- (u:ℂ)= (center K w i i-z)+ (z-u) from (by abel)]
        apply le_trans (mul_le_mul_of_nonneg_left (norm_add_le ..) hc); rw [mul_add]; apply le_trans (add_le_add (coat K w hv hQ closeRe hp hT i) ?_) (b:=(budget+20)*A + 20*A)
        swap
        · refine le_trans (b:=amount c*|u-mass K|) (le_of_eq (by rw [norm_sub_rev,show (u:ℂ)-z= (↑(u-mass K):ℂ) from (Complex.ofReal_sub ..).symm, Complex.norm_real,Real.norm_eq_abs])) (read_toll K hv hp hT)
        linarith
  rw [true_plane X b b' h, ← he]; let F(i:Lat.Fiber):= center K w i i-(u:ℂ);
  have hr:0<(k:ℝ):=by unfold k; positivity
  change _ * ‖(k:ℂ)⁻¹ * (∑ i,center K w i i) - (u:ℂ)‖ ≤ _
  rw [show (k:ℂ)⁻¹*(∑ i, center K w i i)-(u:ℂ) = (k:ℂ)⁻¹ * ∑ i,F i from ?_, norm_mul,norm_inv,Complex.norm_natCast,mul_left_comm (amount c),inv_mul_eq_div];
  · apply (div_le_iff₀ hr).mpr; apply le_trans (mul_le_mul_of_nonneg_left (norm_sum_le ..) hc); rw [mul_sum]; apply (sum_le_sum fun i _=> hl i).trans_eq; rw [sum_const,card_univ,nsmul_eq_mul]; exact mul_comm ..
  unfold F; have ht:(k:ℂ)≠0:=by unfold k; exact_mod_cast Fintype.card_ne_zero (α:=Lat.Fiber)
  rw [sum_sub_distrib,sum_const, card_univ,nsmul_eq_mul,mul_sub,inv_mul_cancel_left₀ ht]

end YM.Massive.Reading
#print axioms YM.Massive.Reading.cost_plane
