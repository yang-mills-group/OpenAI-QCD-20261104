import YM.QCD.Finch.Degree
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
noncomputable def violet (x:Site c):ℂ:=mode (tuning (0:Site c)) (rep x)
noncomputable def corep (x y:Site c):ℂ:=star (violet x)*violet y
noncomputable def modeP (o x:Site c):ℂ:=mode (tuning (0:Site c)) (heel o x)
lemma shineH (o x:Site c): ‖shine o x‖=1:=by rcases shines o x with h|h <;> simp [h]
lemma pick (o i:Site c):violet i=shine o i*violet o *modeP o i:=by
     have h:= concord 0 o (heel o i); rw [ (show o+wrap c (heel o i)=i from by unfold heel; rw [wrap_lift]; abel),wave_root,wave_root] at h
     rw [Stew.shine, Quarry.occ_rays,route_end]; let t:= occ o (heel o i); let x:ℂ:=(c.val:ℂ)⁻¹^2
     have hp: (x*t)*violet i=x*violet o*modeP o i := (Eq.trans (by unfold x t violet; ring) h); rw [mul_assoc x t,mul_assoc x (violet _)] at hp; have he : x≠0:=pow_ne_zero _ (inv_ne_zero (side_ne _)); have hh:= mul_left_cancel₀ he hp
     change _=t*_*_; have hx:t=1∨ t= -1:=by obtain h|h:=shines o i; left; unfold Stew.shine at h; rwa [Quarry.occ_rays,route_end] at h; right; unfold Stew.shine at h; rwa [Quarry.occ_rays, route_end] at h
     rcases hx with h|h <;> simp only [h,one_mul,neg_mul] at hh ⊢; · exact hh
     exact neg_injective (by simp [hh] ) -- order
lemma shiftU (x y:Site c): ‖corep x y‖=1:=by rw [corep,norm_mul,norm_star, violet,violet,mode_real _ _ (keyboard _).1, mode_real _ _ (keyboard _).1,one_mul]
lemma mode_bound (o x:Site c): c.val* ‖modeP o x-1‖≤2*4*Real.pi*(separation x o:ℝ):=by
    let T:=tuning (0:Site c); let d:=separation x o; let A:= heel o x; let R:= Complex.I* ∑ i,T i*(A i:ℂ)
    have ht i: c.val*‖T i‖= Real.pi:=by
       unfold T tuning menu QCD.Free.fixed spacer; simp [Pi.smul_apply,Real.norm_of_nonneg Real.pi_pos.le,lift, mul_comm]; field_simp
    have hh i : ‖(A i:ℂ)‖≤ (d:ℝ):=by
       rw [Complex.norm_intCast]; have hp : |A i|≤ (d:ℤ):=by rw [←Int.natCast_natAbs]; exact_mod_cast (component_le (x-o) i)
       exact_mod_cast hp -- indent issue
    have he : c.val*‖R‖ ≤ 4*Real.pi*d :=by
         rw [show ‖R‖=_ from (show ‖R‖=‖∑ i,T i*(A i:ℂ)‖ from (by unfold R; rw [norm_mul,Complex.norm_I,one_mul]))]; apply (mul_le_mul_of_nonneg_left (norm_sum_le ..) (Nat.cast_nonneg _)).trans; rw [mul_sum]; refine (sum_le_sum (g:=fun _=>Real.pi*d) fun i _=>?_).trans_eq ?_
         · rw [norm_mul, ← mul_assoc, ht]; exact mul_le_mul_of_nonneg_left (hh _) Real.pi_pos.le
         simp; ring
    have hx : ‖modeP o x‖=1:=mode_real _ _ (keyboard _).1
    by_cases hp: ‖R‖≤1; · apply (mul_le_mul_of_nonneg_left (Complex.norm_exp_sub_one_le hp) (by positivity : 0 ≤ (c.val:ℝ))).trans; change _≤2*4*Real.pi*d; linarith only [he]
    have ht': (c.val:ℝ)*1≤ c.val*‖R‖:= mul_le_mul_of_nonneg_left (lt_of_not_ge hp).le (Nat.cast_nonneg _); have ha : ‖modeP o x-1‖ ≤ 2:=(norm_sub_le ..).trans (by rw [hx];norm_num)
    unfold d at *; linarith only [ht'.trans he, mul_le_mul_of_nonneg_left ha (Nat.cast_nonneg (α:=ℝ) c.val)]
lemma crumple (o x y:Site c) : c.val* ‖corep x y-shine o x*shine o y‖ ≤ 2*4*Real.pi*((separation x o:ℝ)+ separation y o):=by
    have hx:star (violet o)* violet o=1:= by
       have hp: ‖violet o‖=1:=mode_real _ _ (keyboard _).1
       rw [mul_comm]; exact (Complex.mul_conj (violet o)).trans (by simp [Complex.normSq_eq_norm_sq,hp])
    rw [corep,pick o x,pick o y,star_mul,star_mul, realSS]
    let M:=modeP o x; let m:=modeP o y
    rw [show star M * _*_ - _=shine o x*(shine o y * ((star M-1)*m+(m-1))) from ?_]; rotate_left
    · calc
         _ = shine o x*(shine o y * ((star (violet o)*violet o)*star M*m-1)):=by unfold M m; ring
         _ = _:=by rw [hx]; ring
    rw [norm_mul, norm_mul, shineH, shineH, one_mul,one_mul]; apply (mul_le_mul_of_nonneg_left (norm_add_le ..) (Nat.cast_nonneg _)).trans; rw [norm_mul,show ‖m‖=1 from mode_real _ _ (keyboard _).1,show ‖star M-1‖=‖M-1‖ by rw [← star_one ℂ,← star_sub,norm_star,star_one],mul_one,mul_add,mul_add]; exact add_le_add (mode_bound ..) (mode_bound ..)
end YM.QCD.Finch
