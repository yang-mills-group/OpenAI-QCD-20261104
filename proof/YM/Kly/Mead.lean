import YM.Kly.Warm
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
variable (r:Future F t₀)
noncomputable def matq(r:Future F t₀) : V.H.Op→L[ℂ]ℂ := (innerSL ℂ V.omega).comp (ContinuousLinearMap.apply ℂ V.H (V.GNS.plant r))
local notation "Z"=>matq (V:=V) r
noncomputable def extraZ (s:E4)(d:ℝ≥0)(r:Future F t₀):= carry (raised t₀ d r.val) (-s)
local notation "T"=> extraZ s d r
include P H Y
lemma queue (h:Padded s d x): distinct (realize v x++T)∧ Z (mac P v s d x)= pointMoment S (realize v x++T):=by
     let w:=realize v x; have hv:= (in_region d v _).mpr (presume H _ h) -- syntax
     have he:(entering hv r).val= carry (realize v x++T) s:=by unfold entering extraZ linked; rw[distribute,paths,neg_add_cancel,rest,cart]
     have hc: distinct (realize v x++T):=by
           have hp:= (entering hv r).property.1; rw[he] at hp; simpa using (still hp (-s))
     refine ⟨hc,?_⟩; change inner ℂ (V.GNS.plant _) (P.place _ _ (V.GNS.plant r)) = _; rw[P.reads hv, V.GNS.measure]; change pointMoment S (entering hv r).val=_; rw[he,invariance Y hc s]
variable {y:Points (n+1)}(Vq:Fin n→F.W) (u v':F.W)
noncomputable abbrev headZ (s:E4)(d:ℝ≥0)(y:Points (n+1))(Vq:Fin n→ F.W)(r:Future F t₀):Cluster F:= realize Vq (Points.tail y)++ extraZ s d r
local notation "Go"=> headZ s d y Vq r
omit H P Y
lemma kind (x:Points (n+1)) (v:Fin n→ F.W)(s:F.W): realize (Fin.cons s v) x= (x 0,s)::realize v (Points.tail x):= by unfold realize; simp only[List.ofFn_succ,Points.cons,points_apply,Fin.cons_zero,List.cons.injEq,true_and, Fin.cons_succ]; rfl
lemma main (z:Cluster F)(b:E4)(w:F.W) : pointMoment S ((b,w)::z)= S _ (Points.cons b (positions z)) (Fin.cons w (tokens z)):=by rw [←readAt,kind]; congr 1; refine congr_arg₂ List.cons rfl ?_; rw [show Points.tail (Points.cons b (positions z))=positions z from (by ext1 i; simp [Points.cons,Points.tail]),knit]
lemma sault(hχ:∀ y∈tsupport χ, InsideTimes s d y)(hx: Physics.Window y χ): Physics.Window (Points.cons (y 0) (positions Go)) χ:=by
      have ht(p)(hp:p∈Go): p.1∉ tsupport χ:=by
            rcases List.mem_append.mp hp with h|h; · obtain ⟨j,rfl⟩:= List.mem_ofFn.mp h; exact hx.2.2.2 _
            intro hh; obtain ⟨u,hu,rfl⟩:= List.mem_map.mp h; obtain ⟨z,hz,rfl⟩:= List.mem_map.mp hu; have hp:= (hχ _ hh).2; have hv:= r.property.2 _ hz; dsimp only at hp
            simp only [PiLp.add_apply,PiLp.neg_apply,PiLp.smul_apply,basis_eq, ↓reduceIte,smul_eq_mul,mul_one] at hp; linarith
      exact ⟨hx.1,hx.2.1,hx.2.2.1,fun j=> ht ((Go).get j) (List.get_mem ..)⟩ -- Go.get fails dot
include H P Y
noncomputable abbrev Yaz (s:E4)(d:ℝ≥0)(y:Points (n+1))(Vq:Fin n→F.W)(r:Future F t₀):Points ((headZ s d y Vq r).length+1):= Points.cons (y 0) (positions (headZ s d y Vq r))
local notation "Ψ"=> Yaz s d y Vq r
lemma atJ (h:Padded s d y) : Ψ∈conf _ ∧ Z (mac P (Fin.cons u Vq) s d y)= S _ Ψ (Fin.cons u (tokens Go)):=by
     obtain ⟨hP,hq⟩:=queue P H Y y (Fin.cons u Vq) r h; rw [kind y] at hP hq
     refine ⟨?_,hq.trans (main ..)⟩; apply (realized (Fin.cons u (tokens Go)) _).1; rw [kind]; change distinct (F:=F) ((y 0,u)::realize (tokens Go) (Points.tail _)); unfold Yaz; rw [show Points.tail (Points.cons (y 0) (positions Go))= positions Go from (by ext i; simp[Points.cons,Points.tail]),knit]; exact hP
lemma atChord (z:E4)(h:Padded s d (Points.cons z y)) : Z (mac P (Fin.cons u (Fin.cons v' Vq)) s d (Points.cons z y))= S ((Go).length+2) (Points.cons z Ψ) (Fin.cons u (Fin.cons v' (tokens Go))):=by
     have ht:= (queue P H Y (Points.cons z y) (Fin.cons u (Fin.cons v' Vq)) r h).2; have hz : Points.tail (Points.cons z y)= y := by ext1 i; simp [Points.cons,Points.tail]
     rw [ht,kind, hz, kind]; rw [←readAt, kind, show Points.tail (Points.cons z Ψ)=Ψ from (by ext1 i; simp[Points.tail,Points.cons]),kind, show Points.tail Ψ=positions Go from (by unfold Yaz; ext1 i; simp [Points.tail,Points.cons]),knit]; rfl
end YM.Massive.Bridge.Kly
#print axioms YM.Massive.Bridge.Kly.sault
#print axioms YM.Massive.Bridge.Kly.atChord
#print axioms YM.Massive.Bridge.Kly.atJ
