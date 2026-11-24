import YM.Gust.Apex
set_option maxHeartbeats 780000
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Gust
open Analysis Function Set Filter MeasureTheory Table Work.A05 Tarn Tarn.Choir UV
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius ComplexOrder Matrix Classical
variable {Q: Choir}{C:Sequence}{P:Calibration C}{d m n:ℕ}{x:Points (n+1)}{χ:E4→ℝ}{V:E4→E4}
variable {S:Axis→Axis→ Q.W}{F:Pollens P Q}(hP:Foil P Q F) (hQ:Q.Domestic) (A:Axle Q S)
variable (B:Q.W)(p:Fin n→ Q.W)(a b:Axis)(g:Ortho.Skew)
include hQ
lemma Axle.drift (hx:x∈conf _)(hw:Window x χ) : headG p x (A.jet g (Q.arc b B)-Q.arc b (A.jet g B))=∑ c:Axis,(g.val c b:ℂ)*gradG S χ c x p B:=by
   have hh : (fun t=> spin S χ g (Ward.cast x 0 b t) p B) =ᶠ[𝓝 0] fun t=> Q.total _ (Ward.cast x 0 b t) (Fin.cons (A.jet g B) p):=by
         filter_upwards [Work.A02.stable hx hw b] with t he; exact (A.relation g B n _ _ he.1 he.2 p).trans (heads p _ _)
   have he:= (Gust.deriv_head hQ hx b (A.jet g B) p).unique (hh.hasDerivAt_iff.mp (Gust.deriv_shellSpin hQ hx hw b S g B p))
   rw [map_sub,heads _ _ (Q.arc b _),he,← A.relation g (Q.arc b B) n _ χ hx hw]
   unfold spin; abel
-- vector translation.V.
structure Vane (A:Axle Q S) where
  edge: Axis→ Q.W→ₗ[ℂ]Q.W
  snaps (n:ℕ)(v:Points (n+1))(p:Fin n→Q.W)(χ)(hx:v∈conf _)(hw:Window v χ)(c:Axis)(p0:Q.W):gradG S χ c v p p0=headG p v (edge c p0)
local notation "WΩ"=> StressFlux.Annular.turn
lemma Axle.stemP : Nonempty (Vane A):=by
       choose b h using fun a:Axis=>exists_ne a
       let D (a:Axis):= Ortho.plane a (b a)
       let p(c:Axis):=(A.jet (D c)).comp (Q.arc (b c))-(Q.arc (b c)).comp (A.jet (D c))
       refine ⟨⟨p,fun n v q χ hx hw c p0=>?_⟩⟩
       have hv:= A.drift hQ p0 q (b c) (D c) hx hw; change _= headG _ _ (_- _); rw [LinearMap.comp_apply,LinearMap.comp_apply,hv,Finset.sum_eq_single_of_mem c (Finset.mem_univ c)]
       · simp [D,Ortho.plane,Matrix.single_apply,h,Ne.symm (h c)]
       · intro j _ ht; simp [D,Ortho.plane,Matrix.single_apply,h,ht, Ne.symm (h c),Ne.symm ht]
variable (E: Vane A)
include hP hQ
lemma Vane.sparks: A.jet g (Q.arc b B)-Q.arc b (A.jet g B) = ∑ c:Axis,(g.val c b:ℂ) • E.edge c B := by
       apply detected hP; intro n p x hx; obtain ⟨χ,hχ⟩:= Work.A01.exists_window x hx
       rw[A.drift hQ B p b g hx hχ,map_sum]; apply Finset.sum_congr rfl; intro i _; rw[map_smul,E.snaps _ _ _ _ hx hχ]; rfl
variable {w:E4}(W:E4→E4)
-- homogeneous motion costs.
lemma sMotion(a b:Ortho.Skew)(hx:x∈conf _)(hw:Window x χ) : about S χ (WΩ (a+b)) x (Fin.cons B p)= about S χ (WΩ a) x (Fin.cons B p)+ about S χ (WΩ b) x (Fin.cons B p):=by
       let T (a:Ortho.Skew)(c d:Axis):= termG S χ (fun y=>StressFlux.Annular.turn a (y-x 0)) x (Fin.cons B p) c d
       have h (a:Ortho.Skew)(c d:Axis) : Integrable (T a c d) := termG_integrable S χ (fun y=> M4.move a.val (y-x 0)) x (Fin.cons B p) hQ hx hw c d (((StressFlux.Annular.turn_motion a).smooth d).continuous.comp (continuous_id.sub continuous_const))
       have hh(c d:Axis)(y:E4): T (a+b) c d y= T a c d y + T b c d y:=by simp[T,termG, StressFlux.Annular.turn_add,mul_add,add_mul]
       change -(∑ c,∑ d, ∫ y,T (a+b) c d y)= -(∑ c,∑ d, ∫ y,T a c d y) + -(∑ c,∑ d, ∫ y,T b c d y)
       simp_rw [hh,integral_add (h a ..) (h b ..),Finset.sum_add_distrib]; abel
omit hQ hP
lemma kMotion(a:Ortho.Skew)(c:ℝ): about S χ (WΩ (c • a)) x (Fin.cons B p)= (c:ℂ) • about S χ (WΩ a) x (Fin.cons B p):=by
       let T (t:Ortho.Skew)(b d:Axis):= termG S χ (fun y=>StressFlux.Annular.turn t (y-x 0)) x (Fin.cons B p) b d
       have h(b d:Axis)(y:E4): T (c • a) b d y= (c:ℂ)* T a b d y:=by simp only[T,termG,StressFlux.Annular.turn_smul,PiLp.smul_apply, smul_eq_mul,Complex.ofReal_mul]; ring
       change -(∑ b,∑ d, ∫ y, T (c • a) b d y)= (c:ℂ)* -(∑ b,∑ d, ∫ y,T a b d y)
       simp_rw [h, integral_const_mul,mul_neg,Finset.mul_sum]
-- whole W addition+scalar to get Lie eventually proper. Avoid Real scalars instance.
include hQ hP
lemma Axle.addP (g v:Ortho.Skew): A.jet (g+v)= A.jet g +A.jet v:=by
       refine LinearMap.ext fun x=> detected hP _ _ ?_; intro n p z hz; obtain ⟨χ,hχ⟩:=Work.A01.exists_window z hz
       rw [← A.relation _ x n z χ hz hχ,sMotion hP hQ x p g v hz hχ]; rw[A.relation g x n z χ hz hχ,A.relation v x n z χ hz hχ,LinearMap.add_apply,map_add] -- rw notation?
omit hQ
include hP
lemma Axle.scaleP(g:Ortho.Skew)(c:ℝ) : A.jet (c • g)=(c:ℂ) • A.jet g:=by
       refine LinearMap.ext fun x=> detected hP _ _ ?_; intro n p z hz; obtain ⟨χ,hχ⟩:=Work.A01.exists_window z hz
       rw [← A.relation _ x n z χ hz hχ,kMotion,A.relation g x n z χ hz hχ,LinearMap.smul_apply,map_smul]
end YM.Massive.Gust
#print axioms YM.Massive.Gust.Axle.addP
#print axioms YM.Massive.Gust.Axle.scaleP
#print axioms YM.Massive.Gust.Vane.sparks
#print axioms YM.Massive.Gust.Axle.stemP
