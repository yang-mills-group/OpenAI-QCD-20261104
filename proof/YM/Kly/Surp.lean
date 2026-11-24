import YM.Kly.Mead
set_option autoImplicit false
set_option maxHeartbeats 610000
noncomputable section
namespace YM.Massive.Bridge.Kly
open Function Set Filter Analysis
open OS (Cross)
open Fields (pointMoment distinct)
open scoped Topology BigOperators InnerProductSpace NNReal ContDiff ComplexOrder
open MassiveTwoEstimates Spinor Spinor.Lift
variable {F:Fields} {S:F.Kernel}{V:Chamber S timeAxis}(P:Spread V)
variable (H:Steady V) (Y:Fields.Euclidean S)(R:Angular S) {Q:Sequence}{C:Calibration Q}(E:F.System C){X:Bases F}{M':Momentum F}(U:X.Content C M')
variable {n:ℕ}(x:Points n)(v:Fin n→F.W)
local notation "t₀"=>timeAxis
local notation "Ω"=> P.algebra
variable (A:V.VacuumOp →L[ℂ]ℂ) (X': P.algebra→⋆ₐ[ℂ]ℂ)(hX:Continuous X')
local notation "G"=> bloom P H X'
variable {s:E4}{d:ℝ≥0}{χ:E4→ℝ}
open Work.B09 MeasureTheory Lift
include P E Y H hX
variable (ha:∀ x:F.W,F.adj t₀ (F.parity x)=F.parity (F.adj t₀ x))
include R ha
lemma paidR (M N: V.H.Op)(hM:Cpr (V:=V) M∈ P.algebra)(hN:Cpr (V:=V) N∈P.algebra)(hx:∀ r:Future F t₀, matq r M=matq r N): Cpr (V:=V) M=Cpr (V:=V) N:=by
        let A: P.algebra:=⟨_,hM⟩; let B: P.algebra:=⟨_,hN⟩; let L:= M-N; have hp(r:Future F t₀): inner ℂ V.omega (L (V.GNS.plant r))=0:=by change matq r L=0; unfold L; rw [map_sub,hx,sub_self]
        let T:V.VacuumOp:=(Cpr (V:=V)) L; have he:T=(A-B).val:=map_sub ..; let O:=V.omega0
        have ht(v:V.H) : inner ℂ V.omega (L v)=0:=V.GNS.whole.induction_on v (isClosed_eq (by fun_prop) continuous_const) (fun i=>by
              induction i using Finsupp.induction_linear with
              | add i j hi hj=> simp only[map_add,inner_add_right,hi,hj,add_zero]
              | zero=> simp
              | single i c=> simp only[YM.Kernel.Gram.stems,Finsupp.linearCombination_single,map_smul,inner_smul_right,hp,mul_zero]) -- syntax order
        have hT:T.adjoint V.omega0=0:=by
             apply ext_inner_right ℂ; intro x; rw[ContinuousLinearMap.adjoint_inner_left]; change inner ℂ O (V.D.orthogonalProjectionOnto _)=_; rw[Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left]; exact (ht x.val).trans (inner_zero_left ..).symm
        have hb:A=B:= sub_eq_zero.mp (by
             have h:= tooth P H Y R E ha (star (A-B)) (show (star (A-B)).val O=0 from (by rw[he] at hT; exact hT)); exact star_eq_zero.mp h)
        exact congr_arg Subtype.val hb
omit ha R
variable {y: Points (n+1)}(p:E4→ E4)(hp:Continuous p) (k:Physics.Window y χ)(T:Momentum F)
local notation "qz" i:arg=> fun z:E4=> (p (z-y 0) i:ℂ)
include hp k
lemma pushes (v:Fin (n+2) → F.W)(hx:Padded s d y)(hy:∀ x∈ tsupport χ,InsideTimes s d x) (i j:Axis) (φ:V.VacuumOp →L[ℂ]ℂ)(hφ:∀ x:P.algebra,φ x.val=X' x): Integrable (fun z=> ((D (basis i) χ z*p (z-y 0) j:ℝ):ℂ) * G _ (Points.cons z y) v)∧ (φ.comp Cpr) (∫ z,filled P i χ (qz j) s d v y z)=∫ z, ((D (basis i) χ z*p (z-y 0) j:ℝ):ℂ) * G _ (Points.cons z y) v:=by
       have hc:Continuous (qz j):= by fun_prop
       have he:= march_f P H Y E v hy k hx (qz j) hc i (φ.comp Cpr) (fun z=> G _ (Points.cons z y) v) (fun t ht=>by
               have h:= padded_shell (show Table.Window _ _ from k) hx hy ht; change φ (Cpr _) = X' _; rw [← hφ,activeM P H (Points.cons t y) v s d h.2.1 (presume H _ h)])
       simpa only [Work.B09.weight,Complex.ofReal_mul] using he
include R ha
variable (α:Module.End ℂ F.W)(hQ:∀ (n:ℕ)(x:Points (n+1))(hx:x∈conf (n+1)) u χ, Physics.Window x χ → Physics.shell T S x u χ p=S (n+1) x (update u 0 (α (u 0))))
include hQ
lemma onwards (u:Fin (n+1) → F.W)(hx:y∈conf _): Physics.shell T (G) y u χ p= G _ y (update u 0 (α (u 0))):=by
       obtain ⟨s,d,hy,hz⟩:= exists_padded hx k.2.1; obtain ⟨φ,hφ⟩:= armA P H X' hX
       let X(i j:Axis) : Fin (n+2)→ F.W:= Fin.cons (T i j) u
       let I(i j:Axis): V.H.Op:= ∫ z, filled P i χ (qz j) s d (X i j) y z; let Y:= Fin.tail u; let m:=u 0 -- Y name collision.Y!
       let M:= mac P (update u 0 (α m)) s d y; let N:= -(∑ i:Axis,∑ j:Axis,I i j)
       have ht: Cpr (V:=V) M∈P.algebra:=by unfold M; rw [←activeM P H y _ s d hx (presume H _ hy)]; exact Subtype.property _
       let Ch:=φ.comp (Cpr (V:=V)); have hc(j:Axis) : Continuous (qz j):=by fun_prop
       have hV:Cpr (V:=V) N=Cpr (V:=V) M:=by
            apply paidR P H ‹Fields.Euclidean S› R E X' hX ha -- wrong order
            · unfold N; rw [map_neg,map_sum]; apply (P.algebra).neg_mem; refine (P.algebra).sum_mem fun i _=>?_ ; rw [map_sum]; exact (P.algebra).sum_mem fun j _=> inAlgebra P H ‹Fields.Euclidean S› E _ hz k hy _ (hc j) i
            · exact ht
            intro r; let Z:= Yaz s d y Y r; let B(u:F.W) : Fin ((headZ s d y Y r).length+1)→F.W:= Fin.cons u (tokens (headZ s d y Y r))
            have hb : u= Fin.cons m Y:= (Fin.cons_self_tail ..).symm
            have hZ:= atJ P H ‹Fields.Euclidean S› r Y (α m) hy; have hf:= hQ _ Z hZ.1 (B m) _ (sault r Y hz k); have hu (i j:Axis): matq r (I i j)= ∫ z, ((D (basis i) χ z*p (z-y 0) j:ℝ):ℂ)*S _ (Points.cons z Z) (Fin.cons (T i j) (B m)) :=by
                   let f(z:E4):ℂ:=S _ (Points.cons z Z) (Fin.cons (T i j) (B m)); apply Eq.trans (march_f P H ‹Fields.Euclidean S› E (X i j) hz k hy (qz j) (hc j) i (matq r) f ?_).2
                   · unfold weight f; simp only [Complex.ofReal_mul]
                   intro t ht; unfold X; rw [hb]; exact atChord P H ‹Fields.Euclidean S› r Y (T i j) m t (padded_shell (show Table.Window _ _ from k) hy hz ht)
            unfold N M; rw [hb,Fin.update_cons_zero,hZ.2, map_neg,map_sum]; simp_rw [map_sum,hu]; apply hf.trans; rw [show B m 0=m from Fin.cons_zero _ _, show update (B m) 0 (α m)= Fin.cons (α m) (tokens (headZ s d y Y r)) from by unfold B; rw [Fin.update_cons_zero]]; -- β -- line hp should Z.0 and Fin.V. update eq not def
       have hv(i j:Axis):= (pushes P H ‹Fields.Euclidean S› E X' hX p hp k (X i j) hy hz i j φ hφ).2 -- placeholder
       unfold Physics.shell; change -(∑ i:Axis,∑ b:Axis,∫ z, ((D (basis i) χ z*p (z-y 0) b:ℝ):ℂ)* G _ (Points.cons z y) (X i b))=_; simp_rw [show ∀ i b:Axis,(∫ z, ((D (basis i) χ z*p (z-y 0) b:ℝ):ℂ)* G _ (Points.cons z y) (X i b))= Ch (I i b) from fun i b=>(hv i b).symm, ← map_sum]; rw[←map_neg]; change φ (Cpr N)= X' (meter P H _ y (update u 0 (α m))); rw [← hφ,activeM P H _ _ _ _ hx (presume H y hy),hV]
end YM.Massive.Bridge.Kly
#print axioms YM.Massive.Bridge.Kly.onwards
