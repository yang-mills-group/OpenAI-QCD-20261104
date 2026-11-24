import YM.QCD.Raft.Pride

/-! # axial reflection of the probe and orientation orbit. no infrared growth used here -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Raft
open Lattice Wilson Function Finset Filter Metric RG Precision Bloch Laurent
open Extra Iteration QCD.Smoke Work.F08 Work.F03 Exterior Bid Lat Fog Stationary Eyrie Quarry Tavern Push.Uniform YM.Further.PhysicalPeriodLimitF933 Jacobi Push.Loops
open scoped Topology BigOperators Matrix ContDiff Classical InnerProductSpace ComplexConjugate
variable {c f n:Side}{a:su.Color}{P: Cnr n→ℝ}
def sun (x:Axis):Aim:= Pi.single (coord x) 1
def pointT (n:Side)(i:Axis): Lens n:= vw (step 0) (sun i)
def brace (T:Lens n) (a: su.Color): Cnr n × Cnr n:= (career n 1 a (vision T),career n 1 a (desire T))
def powerR (P:Cnr n→ℝ) (a:su.Color):= pchain (pairR a P)
def supS (P:Cnr n→ℝ) (a:su.Color):= (powerR P a (pointT n 1) (pointT n 1)).re

lemma lockC (s:Signed)(h:s.perm 0=0)(ht:s.flip 0=false): Signed.act s (step 0:Site n)=step 0:=by
  funext i; obtain ⟨i,rfl⟩:= s.perm.surjective i; simp only [Signed.act_at,step_apply]; by_cases hk:i=0; · simp [hk,h,ht]
  have he: s.perm i≠0:= h ▸ s.perm.injective.ne hk -- h rewrite risk
  split <;> simp [hk,he]
lemma little_cell (s:Signed)(h:s.perm 0=0)(ht:s.flip 0=false)(x:Site n): cell (step 0) (s.act x)=cell (step 0) x:= by
  nth_rw 1 [← lockC (n:=n) s h ht]; exact cell_dual s ..
lemma cellG (u : Axis) (hu:u≠0): cell (n:=n) (step 0) (step u)=1:=by
  have h : Matches (strandT (Pearl.beamH n)) (step 0:Site n):=by rw [← causeT,← wrap_step]; exact quant_matches ..
  rw [h.step]; exact sub_eq_zero.mp (faint (Pearl.beamH n) u hu)
lemma footprint (p:Axis)(i:Site n)(d:Axis): pointT n p (i,coord d)=if d=p then cell (step 0) i else 0:=by
  have he : coord p=coord d ↔d=p:= ((axisEquiv.injective.eq_iff).trans eq_comm)
  unfold pointT vw sun; by_cases h:p=d <;> simp [Pi.single_apply,h,Ne.symm, he]
def reflectsG (s:Signed)(x:Axis):ℂ:= if s.flip x then -1 else 1
lemma poised (s:Signed)(h:s.perm 0=0)(ht:s.flip 0=false)(i: Axis)(hp:i≠0)(a:su.Color) :
    orderTurn s (brace (pointT n (s.perm i)) a).1=(brace ((reflectsG s i) • pointT n i) a).1 ∧ orderTurn s (brace (pointT n (s.perm i)) a).2=(brace ((reflectsG s i) • pointT n i) a).2:=by
  let k : Site n:=step 0
  have he : s.perm i≠0:= by rw [← h]; exact s.perm.injective.ne hp -- loop zero
  have hh (j:Axis)(x:Site n) : pointT n (s.perm i) (s.act x,coord (s.perm j))= pointT n i (x,coord j):=by rw [footprint,footprint,little_cell s h ht]; simp only [s.perm.injective.eq_iff]
  have hv(j:Axis)(x:Site n): pointT n (s.perm i) (s.act x-step (s.perm j),coord (s.perm j))= pointT n i (x,coord j):=by
    rw [footprint,footprint]; simp only [s.perm.injective.eq_iff]; split; next hg=> rw [hg,sub_eq_add_neg,cell_add, cell_inverse, cellG _ he, little_cell s h ht]; simp
    rfl
  constructor <;> funext ⟨x,j,b⟩ <;> obtain ⟨j,rfl⟩:=axisEquiv.surjective j <;>
    rw [coord_map, show orderTurn s _ _=_ from flip_price (m:=n) s _ x j b] <;> simp only [coord_map,brace,career_apply,Pi.smul_apply,smul_eq_mul,vision,desire,hh,hv] <;>
    split <;> rename_i hv' <;> by_cases h:j=i <;> simp_all [footprint,Ne.symm,reflectsG]
lemma orbit_pay (s:Signed)(h:Loves P)(he:s.perm 0=0)(ht:s.flip 0=false)(i j :Axis)(hx:i≠0)(hu:j≠0):
    powerR P a (pointT n (s.perm i)) (pointT n (s.perm j))=(reflectsG s i *star (reflectsG s j))* powerR P a (pointT n i) (pointT n j):=by
  apply Eq.trans _ (show powerR P a (reflectsG s i • pointT n i) (reflectsG s j • pointT n j)=_ from ?_)
  swap; · unfold powerR; rw [pcD,pcV,mul_assoc]
  have hi:= poised (n:=n) s he ht i hx a; have hj:=poised (n:=n) s he ht j hu a
  simp only [brace] at hi hj; unfold powerR pchain; simp_rw [pairR_eval _ _ _ _ h.peak,← hi.1,← hi.2,← hj.1,← hj.2, fix_line h (h.vote s)]
lemma orbit_tight (h:Loves P)(i j:Axis)(hx:i≠0)(hu:j≠0)(he:i≠j):powerR P a (pointT n i) (pointT n j)=0:=by
  let C:= powerR P a (pointT n i) (pointT n j)
  have hp:=(orbit_pay (a:=a) (Signed.mirror i) h rfl (by unfold Signed.mirror; simp [hx]) i j hx hu)
  rw [show reflectsG (Signed.mirror i) i= -1 from by simp [reflectsG,Signed.mirror],show reflectsG _ j=1 from by simp [reflectsG,Signed.mirror,he],star_one,mul_one,neg_one_mul] at hp
  change C=-C at hp; change C=0; linear_combination hp/2
lemma orbit_you (h:Loves P)(i:Axis)(hx:i≠0): powerR P a (pointT n i) (pointT n i)=powerR P a (pointT n 1) (pointT n 1):=by
  let S:Signed:=⟨Equiv.swap 1 i,fun _=> false⟩; have H:S.perm 0=0:=Equiv.swap_apply_of_ne_of_ne (by decide) hx.symm
  have hp:=orbit_pay (a:=a) S h H rfl 1 1 (by decide) (by decide); rw [show S.perm 1=i from Equiv.swap_apply_left .., show reflectsG S 1=1 from rfl,star_one,mul_one,one_mul] at hp; exact hp
end YM.QCD.Raft
