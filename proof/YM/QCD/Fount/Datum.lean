import YM.QCD.Fount.Era
import YM.QCD.Octave.Tire
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.QCD.Fount
open Lattice Wilson Function Finset Filter Metric RG Precision Bloch Laurent Extra Iteration QCD.Smoke
open Lat Octave Kit Leaf Tee Port Garden Transfer Orbit Birth Raft LeafM
open Eyrie Stationary Quarry Work.F03 Matrix Flume Pine Revolve Sparks Lat
open YM.Next.Free YM.Further.PhysicalPeriodLimitF933 Jacobi Fog Voyage Bay
open PhysicalNext.Repeat Lapis ConnectedActivityE6 Push Push.Uniform Blaze Brush Poll Coat
open Cove Reggae
open scoped Topology BigOperators Matrix Matrix.Norms.L2Operator ContDiff Classical InnerProductSpace ComplexConjugate
open Raft.ParcelR
variable {i b j k N:ℕ}{E:Patch}{K:KernelChoices}{p:Clip}{η Ω Θ u v t r a A B w ν α s L y u' σ l d :ℝ} {M:ParcelR}{f c:Side}{S:StepData c f}
abbrev chalice (R:PathData su)(p:Clip)(W:ℕ→Atom su 2)(α:ℝ)(D:Grid c→Sheet c)(N:ℕ)(s:ℝ)(V:Grid c):EvenA c N:= powerZ c N s (D V)-baker c N (N*(α*secondTerm p R V+ Extra.Iteration.action W V)) -- plus pure elsewhere.
-- difference centered fields; sensor widths not flags
abbrev favor {F:Tree.Forest S.ratio} (ρ: Bid.Dir su c→AxisChart su F)(H:Grid f→EvenA c N) (K:Grid c→EvenA c N)(x:Positions (Uniform.Primary c su)):EvenA c N := (H (Octave.projection F (x,Lapis.orbit F ρ x))-K (represent (Uniform.tint su _ x)))
variable (P:Plan j) (V : Back E K j j p u v) {X Y: SunR M} (Q:Avenue V η Ω Θ)(R:PathData su)
local notation "F"=> V.port.forest i
local notation "ds" =>divides0 V.fly V.chain i
local notation "K₀"=>park V.fly (divides0 V.fly V.chain i) P X.X X.Y t 0
local notation "n"=> V.chain.n i
local notation "Γ"=>fun z:Cnr (V.chain.n i)=> (encamp (V.port.forest i) (V.port.u i) z).1
variable (hR:Rates M s)(hp:Species V.fly (divides0 V.fly V.chain i) w ν r 0 a b (park V.fly (divides0 V.fly V.chain i) P X.X X.Y t 0))(hr:0<r)(ht:0<t)(hx:t≤1)
local notation "Υ"=> fun y=> -Real.log ((K₀ ((Γ) y)).det.re)
local notation "σ₀"=>α • inputSeries p R
local notation "ζ"=> Υ+litG V X.Z.page i- (α • inputSeries p R+Voyage.barG Y.Z.page (V.chain.n i))
include Q hp hR hr ht hx
variable {d' e':ℝ}(he:BirthR M P V Q X Y α)(h:R.Bounds p u v u')(hd:Attached Q.D' R)(hy:Precision.Floor Q.D' p (V.chain.n i) d' e')
local notation "dB"=>FieldB M Y (V.chain.n i) l P V.fly.land
include he h hd hy
-- at matched station all gauge. send all large rare. N real width
set_option synthInstance.maxHeartbeats 70000 in
set_option maxHeartbeats 840000 in
lemma border (hg : 0 < l)(hl:l≤1)(ρ:Bid.Dir su (V.chain.n i) → AxisChart su (V.port.forest i)) (H: V.port.u i=ᶠ[𝓝 0] ρ)(D:ℝ)(hD:1 ≤ D)(hX:(Fintype.card (Primary n su):ℝ)≤ D)(N:ℕ):
   let E':= favor ρ (tonic ds K₀ X.Z.page N d) (chalice R p Y.Z.page α dB N d)
   ContDiffAt ℝ ω E' 0 ∧ fderiv ℝ E' 0=0 ∧ normJ 2 E' 0 ≤ (N:ℝ)*tollS D 2 (3*((Fintype.card (Site (V.chain.n i)):ℝ)*(M.l*Real.exp (-M.w*(localG V i).val)))) ∧ ∃ c:ℝ, E' 0=baker (V.chain.n i) N c:=by
    intro E'; let ζ':= (ζ); have hπ:=franc P V Q hR hp hr ht hx he R h hd hy; change ContDiffAt ℝ ω ζ' _ ∧ _ at hπ
    let L:=(mergeC n).toContinuousLinearMap; let S:=ζ' ∘ L; have hz : ContDiffAt ℝ ω S 0:= (show ContDiffAt ℝ ω ζ' (L 0) from (map_zero L).symm ▸ hπ.1).comp (f:=L) _ L.contDiff.contDiffAt
    have hμ: fderiv ℝ S 0=0:=by unfold S; rw [fderiv_comp,map_zero,show fderiv ℝ ζ' 0=0 from hπ.2.1,ContinuousLinearMap.zero_comp]; rw [map_zero]; exact hπ.1.differentiableAt (by simp); exact L.differentiableAt
    let B : Positions (Primary n su) → Sheet n:= (foam V.fly ds K₀ ∘ Γ) ∘ L
    let B' := castF dB ∘ L
    have hh : Duet B B' := duct L (marked P V Q hR hp hr ht hx he hg hl) (L.contDiff.contDiffAt) (map_zero L)
    let U : ℝ→L[ℝ] EvenA n N:= (-(N:ℝ)) • baker n N
    let U₀:= Real.log ((K₀ 1).det.re); let S':= S+(fun _=> U₀)
    let V₀:=powerZ n N d; let V':= U ∘ S'; let Q':=V'+ (V₀ ∘ B-V₀ ∘ B')
    have hS: ContDiffAt ℝ ω S' 0:=hz.add contDiffAt_const; have hT:= U.contDiff.contDiffAt.comp 0 hS; have ha:= duchy V₀ hh V₀.contDiff.contDiffAt
    have hv: Duet Q' V':=by
       have hh:= ha.add (Duet.together ha.rightF.neg (P:=-(V₀ ∘ B')) EventuallyEq.rfl); simp_rw [← sub_eq_add_neg,sub_self] at hh; have he:= (Duet.together (P:=V') hT EventuallyEq.rfl).add hh; rwa [add_zero] at he
    have hv': Duet E' V':=by
       refine ((Duet.together hv.leftF (Q:=E') ?_).flip.chain hv)
       have hp : Tendsto (Uniform.tint su (Exterior.Body 1 n)) (𝓝 0) (𝓝 0):=by simpa using (Uniform.tint su (Exterior.Body 1 n)).continuous.tendsto 0 -- cast
       filter_upwards [hp.eventually H] with x hx; change V.port.u i _=ρ _ at hx
       let W:= represent (Uniform.tint su _ x); let g:Grid (localG V i):= Γ (mergeC n x) -- notation fun parser
       have hi: Octave.projection F (x,orbit (F) ρ x)=g:=by
          unfold Lapis.orbit Uniform.station; simp only [Function.comp_apply]; rw [← hx]; exact strikes F (V.port.u i) x
       have hW: input su (V.chain.n i) (mergeC n x)=W:= input_mat ..
       unfold E' favor; rw [hi]; unfold Octave.tonic Function.comp mica; rw [map_add]; simp only [gets]; -- use shape
       let Y₀:=α*secondTerm p R W+ Iteration.action Y.Z.page W; let Y' := Real.log (K₀ g).det.re; let w':=Iteration.action X.Z.page g
       have hf: S x= -Y'+w'-Y₀:=by unfold S ζ'; simp only [Function.comp_apply,Pi.sub_apply,Pi.smul_apply,Pi.add_apply,barG,inputSeries,show L x=mergeC n x from rfl,hW]; exact rfl
       let v : EvenA n N:= powerZ n N d (B x); let v':=powerZ n N d (B' x)
       have hK : B' x=dB W:=by unfold B'; simp only [Function.comp_apply,castF]; rw [show L x=mergeC n x from rfl,hW] -- names
       change U (S x+U₀) + (v-v') = _ + v-(powerZ _ N d (dB W)- _)
       rw [hf,← hK]; change -(N:ℝ) • ((_+U₀) • (1:EvenA n N))+(v-v')= Loom.Fleet.wearK n N d (((N:ℝ)*(Y'-U₀-w')) • (1:EvenA n N))+ v-(v' - ((N:ℝ)*Y₀) • (1:EvenA n N)) -- namespace inspect
       let K:=Loom.Fleet.wearK n N d; have hg (s:ℝ): K (s • (1:EvenA n N))=s • 1:= by rw [show K _=s • K 1 from map_smul (K.toLinearMap.restrictScalars ℝ) _ _,map_one]
       rw [hg, smul_smul,show -(N:ℝ)*(-Y'+w'-Y₀+U₀)=N*(Y'-U₀-w')+N*Y₀ from by ring,add_smul]; abel
    refine ⟨hv'.leftF,?_,?_,?_⟩
    · have hV: fderiv ℝ V' 0=0:=by
          unfold V'; rw [fderiv_comp _ U.differentiableAt (hS.differentiableAt (by simp)), show fderiv ℝ S' 0=_ from fderiv_add (hz.differentiableAt (by simp)) (differentiableAt_const _), fderiv_fun_const,Pi.zero_apply, hμ, zero_add,ContinuousLinearMap.comp_zero]
      rw [← hV]; exact ContinuousLinearMap.ext (hv'.paint)
    · rw [normJ, muted hv' _ le_rfl]; apply (U.norm_iteratedFDeriv_comp_left hS (le_top (a:=(↑(2:ℕ):WithTop ℕ∞)))).trans
      let q:= (Fintype.card (Site n):ℝ)*(M.l*Real.exp (-M.w*(localG V i).val)); have hv:=hR.hl
      apply (mul_le_mul_of_nonneg_right (show ‖U‖≤N by unfold U; rw [norm_smul,norm_neg,Real.norm_of_nonneg (by positivity)]; exact mul_le_of_le_one_right (by positivity) (colP ..)) (norm_nonneg _)).trans; apply mul_le_mul_of_nonneg_left _ (by positivity)
      unfold S'; rw [iteratedFDeriv_add_apply (hz.of_le le_top) contDiffAt_const, show iteratedFDeriv ℝ 2 (fun i:Positions (Primary n su)=> U₀) 0=0 from congr_fun (show (iteratedFDeriv ℝ (1+1) (fun i:Positions (Primary n su)=> U₀))= _ from iteratedFDeriv_succ_const ..) 0,add_zero]; exact beads hD hX (mul_nonneg (by positivity) (by positivity)) hπ.1 hπ.2.2
    refine ⟨-(N:ℝ)*S' 0,hv'.meet.trans ?_⟩; change -(N:ℝ) • (baker n N (S' 0))= _; exact (map_smul _ _ _).symm
end YM.QCD.Fount
