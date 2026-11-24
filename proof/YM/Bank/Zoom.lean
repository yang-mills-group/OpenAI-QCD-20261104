import YM.Bank.Bee
/-! finite momentum shift; exact periodic seams. usable on true AP cuts. -/
set_option autoImplicit false
noncomputable section
namespace YM.Bank.Zoom
open Wilson Lattice Function Laurent Bloch Metric Finset Filter
open Next.Free Pilot Pap Osc Bee
open QCD.Pearl (beamH beam0 beamP)
open scoped Topology Matrix BigOperators ComplexConjugate Matrix.Norms.L2Operator
variable {c:Side} {σ:Bool} {p q:Momentum} {α r t:ℝ}
def phaseΔ (c:Side)(z:Cover): Momentum:=fun i=> (beamH c*(z i):ℝ)
lemma earthD (c:Side)(z:Cover): physical (phaseΔ c z):=(physical_iff _).mpr fun _=>rfl
lemma physical_spin {x : Momentum}{y: Cover}(h:physical x):physical (x+reciprocal y):= (physical_iff _).mpr fun i=>by rw [Pi.add_apply,Complex.add_im,(physical_iff _).mp h i]; simp
lemma travels (z: Cover)(p:Site c)(σ:Bool):∃ y:Cover, grid σ (p+wrap c z)+reciprocal y=grid σ p + phaseΔ c z :=by
    obtain ⟨y,h⟩:= cover_of_eq (n:=c) (lift (p+wrap c z)) (lift p+z) (by simp)
    have he : mon (p+wrap c z)+ reciprocal y=mon p+phaseΔ c z:=by
        have hm:=bill c; have hb:= side_ne c
        funext i; have hh:=congr_fun h i; change ((lift p i +z i:ℤ))= _ + c.val • y i at hh
        have H : (↑(lift p i):ℂ)+z i = (lift (p+wrap c z) i:ℂ)+(c.val:ℂ)*y i:=by exact_mod_cast hh
        simp only [Pi.add_apply,mon,Laurent.reciprocal,phaseΔ,Pi.smul_apply,smul_eq_mul,QCD.Pearl.beamH]; push_cast; field_simp; linear_combination -(1:ℂ)*H -- sign
    refine ⟨y,?_⟩; cases σ; exact he
    simp only [grid, if_true, QCD.Flume.shiftPhase]; rw [add_right_comm _ _ (Laurent.reciprocal _),he]; abel
lemma star_jump {p:Momentum}{y:Cover}(hp:p∈baseCube)(h:y≠0): 2*Real.pi ≤ ‖p‖+‖p+reciprocal y‖:=by
    obtain ⟨i,hi⟩:= Function.ne_iff.mp h; change y i≠0 at hi; have hz :1≤ |(y i:ℝ)|:=by rw [abs_nat]; exact_mod_cast (show 1≤ (y i).natAbs by omega)
    have hx : 2*Real.pi≤‖reciprocal y‖:=by
      apply le_trans _ (norm_le_pi_norm _ i); unfold Laurent.reciprocal; simp only [norm_mul,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos,Complex.norm_intCast]; exact le_mul_of_one_le_right (by positivity) hz
    have hp:= norm_sub_le (p+reciprocal y) p; rw [add_sub_cancel_left] at hp; linarith
lemma clears (p:Site c)(σ:Bool)(z:Cover)(h:‖grid σ p + phaseΔ c z‖< Real.pi): grid σ (p+wrap c z)= grid σ p + phaseΔ c z:=by
    obtain ⟨y,hy⟩:=travels z p σ; by_cases hp:y=0; rw [hp, show Laurent.reciprocal (0:Cover)=0 by ext; simp [reciprocal],add_zero] at hy; exact hy -- reciprocal zero
    have he:=star_jump (cubic σ (p+ wrap c z)) hp; rw [hy] at he; have hx:=QCD.Pearl.cap_base (cubic σ (p+wrap c z)); linarith
lemma echo (p: Site c)(z: Cover)(t: Cover)(σ:Bool) : mode (grid σ (p+wrap c z)) t = mode (grid σ p) t*mode (phaseΔ c z) t:=by
    rw [← mode_phase]; obtain ⟨y,hy⟩:= travels z p σ; rw [← hy,mode_phase,mode_periodic,mul_one]
lemma phase_mul (c:Side)(z:Cover)(n:ℕ):phaseΔ c (n • z)=n • phaseΔ c z:=by ext i; unfold phaseΔ; simp only [nsmul_eq_mul,Pi.mul_apply,Pi.natCast_apply]; push_cast; ring
lemma inland_small {c:Side}{w:ℕ}(z:Cover)(i:ℕ)(h:i≤w):
     ‖phaseΔ c (i • z)‖ ≤ w * ‖phaseΔ c z‖ :=by
    rw [phase_mul]; exact (norm_nsmul_le ..).trans (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr h) (norm_nonneg _))
lemma near_bank {p:Site c}{z: Cover}{w:ℕ}{u:ℝ}(i:ℕ)(hi:i≤w)(hp:‖grid σ p‖≤u)(he:w*‖phaseΔ c z‖≤u)(h:2*u<Real.pi):
     grid σ (p+i • wrap c z)=grid σ p+i • phaseΔ c z ∧ ‖grid σ (p+i • wrap c z)‖≤2*u:=by
    have ht:= (norm_add_le (grid σ p) (phaseΔ c (i • z))).trans ((add_le_add hp ((inland_small _ _ hi).trans he)).trans_eq (by ring : u+u=2*u)) -- remove unnecessary p
    rw [←map_nsmul, clears _ _ _ (ht.trans_lt h)]; exact ⟨by rw [phase_mul],ht⟩
-- seam lower after move
lemma bound_far {p:Site c}{z:Cover}{w:ℕ}(i:ℕ)(hi:i≤w) (hX:Real.pi/2 ≤ ‖grid σ p‖) (hv:w*‖phaseΔ c z‖≤Real.pi/4): Real.pi/4 ≤ ‖grid σ (p+i • wrap c z)‖:=by
    obtain ⟨v,he⟩:= travels (i • z) p σ; rw [map_nsmul] at he; have hp := cubic σ (p+i • wrap c z)
    let q:= grid σ p; let k:= phaseΔ c (i • z); have hi : ‖k‖ ≤ Real.pi/4:= (inland_small _ _ hi).trans hv
    by_cases h:v=0; subst v
    · rw [show Laurent.reciprocal (0:Cover)=0 by ext; simp[Laurent.reciprocal],add_zero] at he; rw [he]
      change _ ≤ ‖q+k‖; change _ ≤ ‖q‖ at hX; have h' : ‖q‖ ≤ ‖q+k‖+‖k‖:=by simpa only [add_sub_cancel_right] using norm_sub_le (q+k) k
      linarith
    have h':= star_jump hp h; rw [he] at h'; change _ ≤ _+‖q+k‖ at h'
    linarith [norm_add_le q k,QCD.Pearl.cap_base (cubic σ p),Real.pi_pos] -- change q
end YM.Bank.Zoom
