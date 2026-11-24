import YM.QCD.Finch.Riff
/-! # Financial projection momentum. mass at half-star epsilon. Doesn't presume recruitment of geometrical label subsets. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Finch
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae Jets Sun Kites
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {I J V:Type}{c f:Side}{N n:ℕ}
open Animals
open Flume Orbit Quarry Folding Further.PhysicalPeriodLimitF933 Macrame PhysicalNext.Repeat Deck Meadow
open Pressure ConnectedActivityE6 Blaze King Push.Uniform
open Brick Dust Grove Entr YM.Next.Free Bloch Laurent QCD.Free
variable {t s τ u :ℝ}{j k:ℕ}{B:BudgetPoint}
noncomputable abbrev chad : Fiber:= ((0,0),0)
noncomputable def stow (F: Sheet c):ℂ:=∑ x:Site c×Site c,corep x.1 x.2 *F (x.1,chad) (x.2,chad)
lemma pStow (F:Sheet c): stow F = (Fintype.card (Site c):ℂ)*peel F (0,chad) (0,chad):=by
    let J:=(chad:Fiber); let U:=leaf c; let D:=(c.val:ℂ)⁻¹^2
    have ht(x y: Site c): corep x y = (c.val:ℂ)^4*star (scarf 0 x)*scarf 0 y:=by
       rw [wave_root,wave_root,star_mul,show star D=D from ?_]; rotate_left
       · unfold D; rw [star_pow]; simp only [show star = (starRingEnd ℂ:ℂ→+*ℂ) from rfl,map_inv₀, map_natCast]
       change star (violet x)*violet y=_; unfold D violet; field_simp
    have hx(x:Site c): star U (0,J) (x,J)=star (scarf 0 x):=by simp only [U,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_apply,bare_leaf,Matrix.one_apply_eq,mul_one]
    have he(y:Lat.Row c): (star U*F) (0,J) y=∑ x:Site c,star (scarf 0 x)*F (x,J) y:=by
       rw [Matrix.mul_apply,Fintype.sum_prod_type]; refine sum_congr rfl fun i _=>?_ ; rw [sum_eq_single J]; exact congr_arg₂ _ (hx ..) rfl
       · intro j _ hz; simp [U,bare_leaf,hz]
       simp
    unfold peel stow; rw [Matrix.mul_apply,Fintype.sum_prod_type,Fintype.sum_prod_type, site_card]; push_cast; rw [mul_sum,sum_comm]; refine sum_congr rfl fun i _=>?_ ; rw [sum_eq_single chad]; rotate_left
    · intro j _ h; simp [bare_leaf,h]
    · simp
    rw [show (star (leaf c)*_) (0,chad) (i,chad)=_ from he (i,J),sum_mul,mul_sum,bare_leaf,Matrix.one_apply_eq,mul_one]; refine sum_congr rfl fun j _=> ?_ ; rw [ht]; ring
variable (o:Site c)(a: Flavor N)(X:EvenA c N)
noncomputable def Hx (x:Site c): Modes c N:= ((x,chad),a)
lemma paidS (W: Site c×Site c→ℂ)(R:ℝ) (h:0≤t)(hr:0≤R)(hp:∀ i:Site c×Site c, ‖W i‖≤R*pieD (Stew.lens o) (tag (Hx a i.1) (Hx a i.2))):
   t^2*‖(∑ i:Site c×Site c,W i*feeF a X (i.1,chad) (i.2,chad))‖ ≤ R*Sen o t X:=by
    let I:=Site c×Site c; let G v:= coef v X.val ; let H v:= starch (Stew.lens (N:=N) o) t v * ‖G v‖; have he(v):0≤ H v:=mul_nonneg (starch_pos _ h _) (norm_nonneg _); let P(i:I):=tag (Hx a i.1) (Hx a i.2); have hx (i:I):(P i).card=2:=by simp [P,Stew.tag]
    have hQ (u v:I)(hs:P u=P v): u=v:=by
       obtain ⟨h1,h2⟩:= (tagged ..).1 hs; let k (i:Modes c N):=i.1.1; exact Prod.ext (congr_arg k h1) (congr_arg k h2)
    have hg (i:I): ‖feeF a X (i.1,chad) (i.2,chad)‖= ‖G (P i)‖:=by
       change ‖bit (Hx a i.1) (Hx a i.2)*G (P i)‖=_; obtain h|h:= bitS (Hx a i.1) (Hx a i.2)<;> rw [h] <;> simp
    let f(i:I):=feeF a X (i.1,chad) (i.2,chad)
    apply (mul_le_mul_of_nonneg_left (norm_sum_le ..) (by positivity : 0≤ t^2)).trans; rw [mul_sum]; simp_rw [norm_mul]; refine (sum_le_sum (g:=fun j=>R*H (P j)) (fun i _=> ?_)).trans ?_
    · unfold H starch; rw [hg i, hx]; exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hp i) (norm_nonneg _)) (sq_nonneg t)).trans_eq (by dsimp only [P]; ring)
    rw [← mul_sum]; refine mul_le_mul_of_nonneg_left ?_ hr; rw [← sum_image (f:=H) (g:=P) (show Injective P from fun _ _=> hQ _ _).injOn]; rw [Sen,Stew.plank,pricesD _ h]; exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun i _ _=> he _
lemma ridesP (x y:Site c): let i:= tag (Hx a x) (Hx a y); let j:=pieD (Stew.lens o) i; 1≤ j ∧ separation x o≤j ∧ separation y o≤j:=by
    intro i j; let q:= i.sup (Stew.lens o); have h : q≤j:= (by change q≤(1+q)^2 ; nlinarith); exact ⟨one_le_pow₀ (by omega), (show separation x o≤ q from le_sup (f:=Stew.lens o) (show Sum.inr (Hx a x)∈ i from (by simp [i,Stew.tag]))) |>.trans h, (show separation y o≤q from le_sup (f:=Stew.lens o) (show Sum.inl (Hx a y)∈ i from (by simp [i,Stew.tag])))|>.trans h⟩
abbrev coz (F:Spike):ℂ:= F (0,0) (0,0)
noncomputable abbrev milk (o:Site c)(F:Sheet c):ℂ := coz (shape o F none)
lemma mw (h:0≤t): t^2 * ‖stow (feeF a X)‖≤Sen o t X ∧ t^2 * (c.val*‖stow (feeF a X)-milk o (feeF a X)‖)≤ 4*4*Real.pi*Sen o t X:=by
    constructor
    · exact (paidS o a X (fun i=>corep i.1 i.2) 1 h zero_le_one (fun i=>by rw [shiftU,one_mul]; exact_mod_cast ((ridesP o a i.1 i.2).1))).trans_eq (one_mul _)
    let F:=feeF a X; let φ (i:Site c×Site c):=((c.val:ℂ)*(corep i.1 i.2-shine o i.1*shine o i.2)) -- inference
    have he(i:Site c×Site c): ‖φ i‖ ≤ 4*4*Real.pi*pieD (Stew.lens o) (tag (Hx a i.1) (Hx a i.2)):=by
        unfold φ; rw [norm_mul,Complex.norm_natCast]; apply (crumple o i.1 i.2).trans
        obtain ⟨h1,h2,h3⟩:= ridesP o a i.1 i.2;
        have hh:= Real.pi_pos; rw [mul_add]; exact (add_le_add (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr h2) (by positivity : 0≤2*4*Real.pi)) (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr h3) (by positivity : 0≤2*4*Real.pi))).trans_eq (by ring) -- ok
    have hv: milk o F=∑ x:Site c×Site c,shine o x.1*shine o x.2*F (x.1,chad) (x.2,chad):=by unfold milk Stew.shape coz; simp only [Matrix.sum_apply,Fintype.sum_prod_type]; refine sum_congr rfl fun i _=> sum_congr rfl fun j _=>?_ ; rw [show Stew.mark o none i j=1 from rfl,mul_one]; rfl
    have hh : (c.val:ℝ)*‖stow F-milk o F‖ = ‖(c.val:ℂ)*(stow F-milk o F)‖:=by rw [norm_mul, Complex.norm_natCast]
    have hf:(c.val:ℂ)*(stow F-milk o F)=∑ i:Site c×Site c,φ i*F (i.1,chad) (i.2,chad):=by rw [hv,stow,←sum_sub_distrib,mul_sum]; apply sum_congr rfl; intro i _; unfold φ; ring
    rw [hh,hf]; exact paidS _ _ _ φ _ h (by positivity) he
end YM.QCD.Finch
