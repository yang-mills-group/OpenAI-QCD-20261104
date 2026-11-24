import YM.Kly.Surp
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
lemma yieldU (T:Momentum F)(ht:Physics.Ward T S): Physics.Ward T G:=by
       refine ⟨?_,?_,?_⟩
       · intro n x hx p χ h v hv i j; obtain ⟨s,d,hp,h'⟩:=exists_padded hx h.2.1; obtain ⟨φ,hφ⟩:=armA P H X' hX; exact (pushes P H Y E X' hX v hv h (Fin.cons (T i j) p) hp h' i j φ hφ).1
       · intro n x hx p χ h i; exact onwards P H Y R E X' hX ha (fun _=>basis i) continuous_const h T (F.partialD i) (fun n x h p χ hw=>ht.translation n x h p χ hw i) p hx -- order
       intro n x hx p χ h g; have hv: Continuous (M4.move g.val):=by exact (Matrix.toEuclideanLin g.val).continuous_of_finiteDimensional
       exact onwards P H Y R E X' hX ha _ hv h T (F.lie g) (fun n x h p χ hw=>ht.rotation n x h p χ hw g) p hx
end YM.Massive.Bridge.Kly
#print axioms YM.Massive.Bridge.Kly.yieldU
