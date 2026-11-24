import YM.Massive.Lining.Ronde
import YM.Source.ODE
/-!
Common calibration section exists in the unrenormalized system. For all horizons
and compatible with any Run. Requires addition of Mixing, selection,
Wick identification of tested (quotient) fields, etc., in full goal. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Lining.Temper
open QCD QCD.Lat Lattice Wilson Massive.Papyrus UV Filter Function Finset Matrix Grass
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators NNReal Classical Kronecker TensorProduct
open Purl Scan Cylinder Paper TensorProduct Ferry SourceRead
namespace Collage
private abbrev cushion:ContDiffBump (0:ℝ):=⟨1/8,1/4,by norm_num,by norm_num⟩
private def weft (x:E4) : ℝ:=∏ i:Axis,cushion (x i)
noncomputable def beacon : Taper where
   χ:=weft
   smooth:=contDiff_prod fun i _=> cushion.contDiff.comp (EuclideanSpace.proj i (𝕜:=ℝ)).contDiff
   near x h:=prod_eq_one fun i _=> cushion.one_of_mem_closedBall (by rw [Metric.mem_closedBall,Real.dist_eq,sub_zero]; exact h i)
   outside i h:= Finset.prod_eq_zero (Finset.mem_univ i) (cushion.zero_of_le_dist (by rw [Real.dist_eq,sub_zero]; exact h))
   interval x:=⟨prod_nonneg (fun _ _=> cushion.nonneg),by unfold weft; rw [← show (∏ _x:Axis,(1:ℝ))=1 by simp]; exact prod_le_prod (fun _ _=> cushion.nonneg) (fun _ _=> cushion.le_one)⟩
   even s x:=by unfold weft; rw [← Equiv.prod_comp s.perm]; apply prod_congr rfl; intro i _; rw [EuPin.signMesh]; split; exact cushion.neg _; rfl
lemma illumination (T:Taper) : ∃ H:TaperHol, H.T=T:=by
   have he (n:Side)(d:ℕ)(J:Labels.Jet su)(h:ℝ)(p:Edge Cover) : ContDiff ℝ 1 (T.connection n d J h p):=by
        have hs : ContDiff ℝ 1 (fun t:ℝ=> T.χ ((n.val:ℝ)⁻¹ • (vector p.1+t • basis p.2))):= (T.smooth.of_le (by simp)).comp (by fun_prop); refine hs.smul ?_
        unfold Source.partConnection; apply ContDiff.const_smul; unfold Source.potential; refine ContDiff.sum fun i _=> ?_; exact ((Tensor.diag_smooth _ _)).comp (by fun_prop)
   choose f hf using fun n d J h p=> Source.Hol.pipes (he n d J h p); exact ⟨⟨T,f,hf⟩,rfl⟩
lemma honors : Nonempty (Source.Hol su) ∧ Nonempty TaperHol:= by obtain ⟨H,h⟩:=illumination beacon; exact ⟨Source.Hol.exists_ode _,⟨H⟩⟩ -- type PProd or And
variable (H:Source.Hol su)
structure Exhibit where
    F (d:ℕ): Flag H d (d/2)
    U (d:ℕ): Kedge H d (d/2)
    t (d:ℕ): Finset Cover
    sel (d:ℕ): Room (F d) (U d) (t d)
    lead (d:ℕ): Label d →ₗ[ℂ] Cylinder.Formula (t d) 6
    label (d:ℕ)(x:Label d)(v:Land): porch (t d) v (lead d x)=glaze (F d) (U d) (t d) v x.val
lemma gains : Nonempty (Exhibit H):=by
   let F(d:ℕ):= Classical.choice (photo H d (d/2)); let U(d:ℕ):=Boat.roller H d _ (F d); choose t ht using fun d=> Room.uniform (F d) (U d); choose Q hQ using fun d=> Ford.effect (F d) (U d) (ht d); exact ⟨⟨F,U,t,ht,Q,hQ⟩⟩
namespace Exhibit
variable {H}
variable (A: Exhibit H)(C:Sequence)(T:TaperHol)
-- knobs later
abbrev CoreMix:= (d:ℕ)→Averaging→ℕ→Label d≃ₗ[ℂ]Label d
variable (sym:RawSym)(M:CoreMix)(u:ℕ→ℕ)
def display : Calibration C where
   sym:=sym
   hol:=H
   test:=T
   stencil:=A.t
   localMap:=A.lead
   candidate d n b:= (Realize.placed (A.t d) n b).comp (A.lead d)
   mix := M
   base := u
local notation "P" => A.display C T sym M u
private lemma placed (d:ℕ)(n:Side)(b:Cover)(x:Label d)(U:Grid n): (P).candidate d n b x U=dart (A.F d) (A.U d) (A.t d) n b U x.val:=by
    let F:=A.F d; let V:=A.t d; let L:=Ferry.belt n V b; change places b (A.lead d x) U=_; unfold places; simp_rw [← porch_eval, A.label]; exact dart_ship ..
set_option maxHeartbeats 600000 in
theorem ready : (P).SectionLaws where
   localizes _ _ _ _ _:=rfl
   seed d x J:= Germ.seed (A.F d) (A.U d) (A.t d) J ((A.sel d).extends_box) x.val (A.lead d x) (A.label d x)
   unit d n b:= by
      ext1 x; rw [A.placed, RawSym.unitActs]; exact Ronde.sunlit ..
   parity d n b x:= by funext V; unfold Action.parity; rw [A.placed,A.placed,RawSym.parityActs]; exact foldG ..
   invariant d n b x k:=by apply ContinuousMap.ext; intro V; change slots 6 k ((P).candidate d n b x (gauge k V)) = (P).candidate d n b x V; rw [A.placed,A.placed,wind_gauge,((label_law _).mp x.property).2]
   pin d n b x p s h:=by funext V; unfold Action.pin; rw [A.placed,A.placed,RawSym.pinActs]; exact wind_echo (A.F d) (A.U d) (A.t d) n b V s (A.sel d).parity p h x.val
   star d n b x a:=by funext V; unfold Action.adj; rw [A.placed,A.placed, RawSym.adjActs]; exact wind_eye (A.F d) (A.U d) (A.t d) n b V a (A.sel d).parity x.val
   charge d n b x:=by funext V; unfold Action.charge; rw [A.placed,A.placed,RawSym.chargeActs]; exact wind_N (A.F d) (A.U d) (A.t d) n b V (A.sel d).parity x.val
   flavor d n b x p:=by funext V; unfold Action.flavor Action.flavorF; rw [A.placed,A.placed,RawSym.flavorActs]; exact strolling ..
   mesons d n i j M x h V:=by rw [A.placed,h]; exact Ronde.stars _ _ _ _ _ i j M (A.sel d).origin
   baryons n i j k x h V:=by rw [A.placed,h]; exact Ronde.nightfall (A.t 9) n V (A.F _) (A.U _) i j k (A.sel _).origin
end Exhibit
open Exhibit
theorem landscapes_rune (H: Source.Hol su)(T:TaperHol)(C:Sequence)(u:ℕ→ℕ)(M:CoreMix)(sym: RawSym): ∃ (P:Calibration C), P.base=u ∧ P.mix=M ∧ P.hol=H ∧ P.sym=sym ∧ P.test=T ∧ P.SectionLaws:=by
   obtain ⟨A⟩:= gains H; exact ⟨A.display C T sym M u,rfl,rfl,rfl,rfl,rfl,A.ready _ _ _ _ _⟩
theorem canopy (C:Sequence)(u:ℕ→ℕ) : ∃ P:Calibration C,P.base=u ∧ P.SectionLaws:= by
   obtain ⟨⟨H⟩,⟨T⟩⟩:= honors; obtain ⟨P,h,-,-,-,-,hp⟩:= landscapes_rune H T C u (fun _ _ _ => LinearEquiv.refl ℂ _) RawSym.exhibit; exact ⟨P,h,hp⟩
end Collage
end YM.Massive.Lining.Temper
#print axioms YM.Massive.Lining.Temper.Collage.canopy
