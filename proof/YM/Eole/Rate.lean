import YM.Eole.Omega
import YM.Pollen.Linda
/-! Sector exchange in the replica polynomial. Use ordered factors. -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Sample.Eole
open QCD QCD.Grass QCD.Cove Lattice Finset Ribbon Cupola Stew Function
open Lattice Wilson Creek Lat Kit NormedSpace RG Cove Filter Run
open Loom Fleet MeasureTheory Ribbon Cupola Plate Ruby
open scoped Topology BigOperators ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {I J A B:Type}[Fintype I][Fintype J][Fintype A][Fintype B]
open Quills
open Further.ShellBirth49.Fusing Collide
open Sway OrbitG Bay Strut Push.Local Push.AbsoluteSums Ursell Gas Graph Patron Kites Ribbon Cupola Plate Plate.Card Relight Ruby Massive.PCAC
variable {c:Side}{D:Type}{n:ℕ}
variable (q:I→Bool) {Pt: BudgetPoint} {t u v w z:ℝ} (s: Finset I)
local notation "X"=> Patio (Keys c n ⊕ Spine I)
local notation "Z"=> Keys c n
open Further.DenseMixedKernels
local notation "T"=>Stitch.Tablet.credits
variable {i j:Site c}{O:BudgetPoint}
lemma translate {d : ℝ} (hh : (separation i j:ℝ) ≤ d) {A : Directions su c} (h : O.dirBound j A) :
    O.dirBound i ((((1+d)^O.power)⁻¹:ℝ) • A) := by
  have hd : 0 ≤ d := (Nat.cast_nonneg _).trans hh
  intro p; let t := (1+d)^O.power; have hp : 0 < t := by unfold t; positivity
  change ‖t⁻¹ • A p‖ ≤ _
  rw [norm_smul_of_nonneg (inv_pos.mpr hp).le,inv_mul_le_iff₀ hp]
  refine (h p).trans ?_
  rw [mul_left_comm, show t=(1+d)^O.power from rfl,←mul_pow]; have hb := O.threshold_pos; gcongr
  have he : (separation p.1 j:ℝ) ≤ separation p.1 i + (separation i j:ℝ) := by exact_mod_cast separation_triangle p.1 i j
  nlinarith [Nat.cast_nonneg (α:=ℝ) (separation p.1 i)]
lemma left_turn {F:Type} [NormedAddCommGroup F][NormedSpace ℝ F] (u : Config su c → F) (v : List (Directions su c)) (a : ℝ) (U : Config su c) :
    leftDerivs u (v.map fun A => a • A) U = a^v.length • leftDerivs u v U := by
  induction v generalizing U with
  | nil => simp [leftDerivs]
  | cons x v ih =>
    simp only [List.map_cons,leftDerivs,ih, deriv_fun_const_smul_field]
    have hi (t : ℝ) : t • a • x = (a*t) • x := by rw [smul_smul, mul_comm]
    simp_rw [hi]
    let G (t : ℝ) := leftDerivs u v (increment U (t • x))
    change a^v.length • deriv (fun t => G (a*t)) 0 = _
    rw [deriv_comp_mul_left, mul_zero, smul_smul,List.length_cons,pow_succ]
lemma turner {V:Grid c}{k: ℝ}{f: Grid c→ Patio (Keys c n⊕Spine I)}(h:Phy t f V (O.dirBound i) O.order v 1)(hp:(separation i j:ℝ) ≤ k): Phy t f V (O.dirBound j) O.order v ((1+k)^O.power):=by
    refine ⟨h.smooth,fun l hl hL=>?_⟩; let A:=(1+k)^O.power; have hk:0≤ k:=(Nat.cast_nonneg _).trans hp; have hv:0<A:=(by unfold A; positivity); let x:= l.map (fun z=>A⁻¹ • z); have hh:x.length=l.length:=List.length_map ..; have hh': x.map (fun z=>A • z)=l:=by simp [x,hv.ne',Function.comp_def]
    have he: T t (leftDerivs f x V) ≤ v:=by simpa only [one_pow,mul_one] using h.paid x (hh.trans_le hl) (fun z hz=> by obtain ⟨j,hj,rfl⟩:=List.mem_map.mp hz; exact translate hp (hL j hj))
    conv_lhs => rw [← hh',left_turn]
    let F:=leftDerivs f x V; have hz:0 ≤ A^x.length:=pow_nonneg hv.le _; rw [show T t (A^x.length • F)=A^x.length*T t F from ?_]; exact (mul_le_mul_of_nonneg_left he hz).trans_eq (by unfold A; rw [hh,mul_comm]); rw [← Complex.coe_smul]; exact (Phy.spiceX ..).trans (by rw[Complex.norm_real,Real.norm_of_nonneg hz]) -- check
-- make products via Algebra-map changeVars CL (non-isometric but multiplicative). Rates absolute. 
set_option maxHeartbeats 650000 in
lemma rotated {p f:Grid c→Patio (Keys c n⊕Spine I)} {U:Grid c}{r:Directions su c→Prop}{s0:ℕ}(h:Phy t p U r s0 u v)(hw:Phy t f U r s0 w z): Phy t (p*f) U r s0 (u*w) (v+z):=by
     let F0:=(changeVars (Matrix.diagonal fun i=> ((Stitch.Tablet.chip t (Keys c n) (Spine I) i):ℂ))).comp (light _)
     let G:= F0.toLinearMap.toContinuousLinearMap.restrictScalars ℝ; have hv(x: X) : ‖G x‖= T t x:=by change _=load (Stitch.Tablet.chip t (Keys c n) (Spine I)) (light _ _); unfold Creek.load wscale; congr!; change changeVars _ _= _; congr!
     have he(Z':Grid c→X)(u v:ℝ)(h:Phy t Z' U r s0 u v): Pitch (G∘ Z') U r s0 u v:=⟨G.contDiff.contDiffAt.comp _ h.smooth,fun l hl hv'=>by rw [show leftDerivs (G∘Z') l U=G (leftDerivs Z' l U) from left_linear G l h.smooth hl,hv]; exact h.paid l hl hv'⟩
     have hL:=Pitch.bilinear (ContinuousLinearMap.mul ℝ (Alg (Z⊕Spine I))) (he p u v h) (he f w z hw) (C:=1) (by intro i j; simp only [one_mul]; exact norm_mul_le ..) zero_le_one
     let n':=p*f; have hP: Push.Local.Chart s0 n' U:=ContDiffAt.mul h.smooth hw.smooth
     refine ⟨hP,fun l hl he'=>?_⟩; rw [←hv,← show leftDerivs (G∘n') l U= _ from left_linear G l hP hl]; have hp:G∘n'=(fun x=> ((ContinuousLinearMap.mul ℝ (Alg (Z⊕Spine I))) ((G ∘ p) x)) ((G∘f) x)):=funext fun x=>map_mul F0 _ _; rw[hp]; simpa only[one_mul] using hL.bounds l hl he' -- maybe as equality functions needs congr
-- chart helpers
private noncomputable def mortar : Fields c n →L[ℂ] Patio (Keys c n⊕Spine I):=by
    let f: Fields c n →L[ℂ] Alg (Z⊕Spine I):= Ribbon.stake Z (burst q s); let g:Alg (Z⊕Spine I)→ₗ[ℂ]Alg (Z⊕Spine I):= (2:ℂ)⁻¹ • ((LinearMap.id:Alg (Z⊕Spine I)→ₗ[ℂ] Alg (Z⊕Spine I))+Grass.grade.toLinearMap); let p:= g.comp f.toLinearMap; exact LinearMap.toContinuousLinearMap (p.codRestrict (roomA _).toSubmodule fun x=> (show Plus (p x) from (plus_grade _)))
lemma marR (x:X)(h:Polite q s x): mortar q s (pluck Z (burst q s) x)=x:=by
    apply Subtype.ext; change (2:ℂ)⁻¹ • (stake Z _ _+Grass.grade (stake Z _ _))= _; rw [show stake Z _ (pluck Z (burst q s) x)=_ from h.exact, (show Grass.grade x.val=x.val from (bright x))]; rw [← two_smul ℂ x.val]; exact inv_smul_smul₀ (by norm_num) _
lemma noble (x:Grid c→ X)(h:∀ i, Polite q s (x i))(c':Grid c)(hc:Chart Pt.order x c') (l:List (Directions su c))(hl:l.length ≤ Pt.order) : Polite q s (leftDerivs x l c'):=by
    apply Polite.of_ranges; intro j hj; let e:=(pluck Z j).restrictScalars ℝ; change e (leftDerivs x l c')=0; rw [← left_linear e _ hc hl]; rw [show e ∘ x=fun _=>0 from funext fun _=> (h _).spectral j hj]; simpa only [ite_self] using! Work.G07.left_const (0:Lat.Fields c n) l c'
variable (f:Grid c→Patio (Keys c n⊕ Spine I))
lemma chartA {S:Support c}(h:∀ i,Polite q s (f i))(c':Grid c)(hc:Healthy Pt.threshold S c')(hz:Sight S i 2 Pt t (pluck (Keys c n) (burst q s)∘ f) u)(he:0<t): Phy t f c' (Pt.dirBound i) Pt.order u 1:=by
     let p':= pluck (Keys c n) (burst q s); let g:=p'∘ f
     have hp':Chart Pt.order f c':=by
         let k:= (mortar (c:=c) (n:=n) q s).restrictScalars ℝ; have hg:Chart Pt.order g c':=hz.use _ hc; rw[show f=k∘g from funext fun i=> Eq.symm (marR q s _ (h _))]; exact k.contDiff.contDiffAt.comp 0 hg
     refine ⟨hp',fun l hl hL=>?_⟩; have hT:=noble q s f h c' hp' l hl; let G:=leftDerivs f l c'; let x:=leftDerivs g l c'; have hw:x=p' G:=left_linear (p'.restrictScalars ℝ) _ hp' hl
     rw [one_pow,mul_one,Stitch.Tablet.polite_bill s _ hT he,show scrape (Keys c n) (burst q s) (leftDerivs f l c').val=x from hw.symm]; exact (viewer i x 2 he).trans (hz.pole c' hc l hl hL)
end YM.MassiveQCD.Sample.Eole
#print axioms YM.MassiveQCD.Sample.Eole.turner
#print axioms YM.MassiveQCD.Sample.Eole.rotated
#print axioms YM.MassiveQCD.Sample.Eole.chartA
