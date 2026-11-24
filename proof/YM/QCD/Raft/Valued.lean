import YM.QCD.Raft.Beam

/-! # reporting cost in physical real combination -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Raft
open Lattice Wilson Function Finset Filter Metric RG Precision Bloch Laurent
open Extra Iteration QCD.Smoke Work.F08 Work.F03 Exterior Bid Lat Fog Stationary Eyrie Quarry Tavern Push.Uniform YM.Further.PhysicalPeriodLimitF933 Jacobi
open scoped Topology BigOperators Matrix ContDiff Classical InnerProductSpace ComplexConjugate
variable {c f n:Side}{a:su.Color}{P: Cnr n→ℝ}
def scoreM (P:Cnr n→ℝ)(a:su.Color)(x:Lens n):=(powerR P a x x).re
def sting (b:Aim):ℝ:=∑ i:Axis, ‖b (coord i)‖^2
lemma sting_boot (H:Loves P)(p:Aim)(he:p (coord 0)=0): scoreM P a (vw (step 0) p)=sting p*supS P a:=by
  have hp : vw (step 0:Site n) p=∑ i:Axis, p (coord i) • pointT n i:=by
    funext ⟨x,a⟩; obtain ⟨k,rfl⟩:=axisEquiv.surjective a; rw [Finset.sum_apply,sum_eq_single k]
    · simp only [Pi.smul_apply,coord_map,footprint,if_true]; unfold vw; exact mul_comm ..
    · intro i _ hi; simp only [Pi.smul_apply,coord_map,footprint,if_neg hi.symm,smul_zero]
    simp
  unfold scoreM powerR; rw [hp,chain_sum]; simp_rw [chain_sum',pcD,pcV]; rw [Complex.re_sum,sting,Finset.sum_mul]; apply sum_congr rfl; intro i _
  by_cases ht:i=0; · subst i; simp [he]
  rw [sum_eq_single i] -- why commute? cstar normalization
  · have h':= orbit_you (a:=a) H i ht
    unfold powerR at h'; rw [h']; rw [← mul_assoc]; -- inspect
    rw [Complex.star_def,Complex.mul_conj, Complex.mul_re]; simp [Complex.sq_norm,supS,powerR]
  · intro b _ hb; by_cases hp:b=0; · subst b; rw [he,star_zero,zero_mul,mul_zero]
    rw [show pchain _ _ _=_ from orbit_tight (a:=a) H i b ht hp hb.symm, mul_zero,mul_zero]
  simp
lemma score_scal (c:ℂ)(x: Lens n): scoreM P a (c • x)= ‖c‖^2 * scoreM P a x:=by
  unfold scoreM powerR; rw [pcD,pcV, ← mul_assoc,Complex.star_def,Complex.mul_conj, Complex.mul_re]; simp [Complex.sq_norm] -- inspect
variable {k j N:ℕ}{Κ : KernelChoices}{F: Next.Free.Flight j k} {X Y:ℕ→Side}{H V:Bed}{T:Towers F.L}{η C D M:ℝ}(h : Signal X Y H V T η C D N)
abbrev expandG (h: Signal X Y H V T η C D N) (i:ℕ)(v:Lens (X i)) := Push.Loops.cmat (installed (Ratio.mk F.L (h.sizes i)) T.A0)*ᵥ v -- fix binder
lemma stoning (b:Aim)(i:ℕ)(P:Cnr (Y i)→ℝ)(hp:Loves P)(a:su.Color): scoreM P a (expandG h i (vw (step 0) b))=∑ l:Site F.L,scoreM P a (vw (burstsG h i l) (stone T b l (pulseG X i))):=by
  let R : ℕ := (X i).val; let g:=Ratio.mk F.L (h.sizes i); let V:=fun l:Site F.L=> burstsG h i l
  have ht:expandG h i (vw (step 0) b)=∑ l:Site F.L,vw (V l) (shortG T b l (pulseG X i)):=by unfold expandG; rw [← wrap_step,vw_raze g (step 0) T.A0 (Row.rights _ _ ((h.deep.2.2.2 [] (Nat.zero_le _)).1) h.more.le),causeT (X i)]; rfl
  rw [ht,scoreM,powerR,chain_sum]; rw [Complex.re_sum]; apply sum_congr rfl; intro l _; rw [chain_sum', sum_eq_single l];
  · rw [pliant b (h:=signal_test h i l), love_add hp]; rfl
  · intro j _ hj; exact page_chain hp _ _ _ _ ((Push.Loops.aliasSite_inj _).ne hj.symm)
  simp
end YM.QCD.Raft
