import YM.Gust.Zap
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Gust
open Function Set Filter Analysis MeasureTheory Table Work.A01 Outer Tarn Tarn.Choir UV
open scoped Topology ContDiff BigOperators Classical
variable {W: Choir}{C:Sequence}{P:Calibration C}{n d:ℕ}
theorem flux_mirror (T:Pollens P W)(H:Foil P W T)(J:Axis → Axis→ W.W)
    (k : Signed) {x : Points (n+1)} (hx : x ∈ conf _) {χ : E4 → ℝ} (hw : Window x χ)
    (V Q : E4 → E4) (hv : ∀ y, Q (Ortho.move k.ortho y) = Ortho.move k.ortho (V y))
    (p:EuPin)(hp:p.Lifts k)(ht:∀ i j,T.spin p (J i j)=((eps k i * eps k j:ℝ):ℂ) • J (k.perm i) (k.perm j))(q : Fin (n+1) → W.W) :
    fluxG J (shifted k.ortho χ) Q (Points.move k.ortho x) (T.spin p ∘ q) =
      fluxG J χ V x q := by
  let E := Ortho.motion k.ortho
  let f := termG J (shifted k.ortho χ) Q (Points.move k.ortho x) (T.spin p ∘ q)
  have hm (a b : Axis) (y : E4) : f (k.perm a) (k.perm b) (E y) = termG J χ V x q a b y := by
    unfold f termG
    rw [show E y = Ortho.move k.ortho y from rfl, shifted_D k hw.1, hv y, move_coordinate]
    by_cases hz : D (basis a) χ y = 0
    · simp [hz]
    have he:= H.discrete _ _ (separated_of_D hx hw hz) p k hp (Fin.cons (J a b) q)
    rw [show p.coord= _ from hp,move_cons,comp_cons,ht a b,← heads, map_smul, smul_eq_mul,heads] at he
    rw[←he]; push_cast; ring
  have hi (a b : Axis) : (∫ y, f (k.perm a) (k.perm b) y) = ∫ y, termG J χ V x q a b y := by
    rw [← E.measurePreserving.integral_comp E.toHomeomorph.measurableEmbedding]
    simp_rw [hm]
  unfold fluxG
  apply congr_arg Neg.neg
  change ∑ a, ∑ b, (∫ y, f a b y) = _
  rw [← Equiv.sum_comp k.perm (fun a => ∑ b, (∫ y, f a b y))]
  apply Finset.sum_congr rfl; intro a _
  rw [← Equiv.sum_comp k.perm (fun b => (∫ y, f (k.perm a) b y))]; simp_rw [hi]
variable (B:Axis×Axis→W.W){T:Pollens P W}(hW:W.Domestic)(H:Foil P W T)(J:Axle W (fun a b=>B (a,b)))(hB:Tarn.ChargeQ.Persona T B)
include H hB
lemma pivotP (s:Signed)(p:EuPin)(hp:p.Lifts s) (a b:Axis): T.spin p (B (a,b))=((eps s a*eps s b:ℝ):ℂ) • B (s.perm a,s.perm b):=by
       have h(i:Axis):eps s i= signT s i:=by unfold eps; rw[Signed.matrix_at,if_pos rfl]; rfl
       exact Eq.trans (hB.tense.geo p s hp a b) (by rw[h,h])
lemma liven(s:Signed)(p:EuPin)(hp:p.Lifts s)(g:Ortho.Skew)(w:W.W): J.jet (Org.orients s g) (T.spin p w)=T.spin p (J.jet g w):=by
       apply detected H; intro n q x hx; let Q:= Points.move s.ortho⁻¹ x; have hQ:=Points.move_in s.ortho⁻¹ hx; let v:= (T.spin p).symm ∘q; obtain ⟨χ,hχ⟩:= Work.A01.exists_window Q hQ; let f:= shifted s.ortho χ; have ht: x= Points.move s.ortho Q:=by ext1 i; simp[Q]
       have he:Table.Window x f:= ht ▸ window_move _ hχ; have h0:T.spin p∘ v=q:= funext fun i=>(T.spin p).apply_symm_apply _
       rw [← J.relation _ (T.spin p w) _ _ f hx he]
       have ht' :=flux_mirror (W:=W) T H (fun a b=>B (a,b)) s hQ hχ (Work.A01.orbital g (Q 0)) (Work.A01.orbital (Org.orients s g) (x 0)) (fun y=>by unfold orbital; apply Eq.trans _ (move_rotation s g (Q 0) y); rw [ht]; rfl) p hp (pivotP B H hB _ p hp) (Fin.cons w v)
       -- avoid rewriting x itself on RHS tail
       rw [show Points.move s.ortho (Points.move s.ortho⁻¹ x) = _ from ht.symm,Fin.comp_cons,h0] at ht'
       refine Eq.trans ht' (Eq.trans (J.relation g w n Q χ hQ hχ v) ?_); rw [heads,heads,← H.discrete (n+1) _ hQ p s hp,Fin.comp_cons,h0, show p.coord=s.ortho from hp,show Points.move s.ortho (Points.move s.ortho⁻¹ x) = _ from ht.symm] -- ↔
end YM.Massive.Gust
#print axioms YM.Massive.Gust.liven
