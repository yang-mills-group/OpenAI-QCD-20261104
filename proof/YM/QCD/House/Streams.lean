import YM.QCD.House.Rights

/-! # Forest purchases and wash budgets. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Loom.Fleet
open ConnectedActivityE6
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets Horticulture
open Mixed Reserves Trees Beam Cove Leaf Lat PhysicalNext.Repeat.Greenbelt
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical PhysicalNext.Repeat.Greenbelt
variable {c f L:Side}{S:StepData c f}{T:Tube su S}{P:Teller su}{δ β τ μ W C:ℝ} {R:Rep su f}{F Z:Tree.Forest S.ratio}{Q:Target su P}{o :Target.Order su W}
variable {H:Cash W τ μ L Q o C T R}{ι:Type}{N:ℕ}
local notation "I"=> Pipe.Clump S ι
local notation "C'"=>Coat T
variable (Y:Fleet H ι N)
set_option quotPrecheck false
open Art Blaze Polar Shield Frond
open Grass Cove Lat GasP Filter Ursell Graph
open scoped Matrix Kronecker
variable {w c' δ t r:ℝ} (a:ℝ)
-- Real CLM structure
noncomputable def wearK (c:Side)(N:ℕ)(t:ℝ):EvenA c N→ₐ[ℂ] EvenA c N :=car (changeVars (Matrix.diagonal (fun _=>(t:ℂ)))) (fun x h=> (exterior_parity _ x).trans (congr_arg (fun s=> (changeVars ..) s) (show grade x=x from h))) -- edit
noncomputable def songT (t:ℝ):EvenA c N→L[ℝ] EvenA c N:=LinearMap.toContinuousLinearMap ((wearK c N t).toLinearMap.restrictScalars ℝ)
lemma skill (X:EvenA c N):‖token c N a X‖= ‖wearK c N a X‖:=rfl
lemma wit (X: EvenA c N)(u v:ℝ)(hr:u*v=1): wearK c N u (wearK c N v X)=X:=by
    apply Subtype.ext; change changeVars _ (changeVars _ X.val)=X.val; rw [← AlgHom.comp_apply,← change_mul]; convert! (AlgHom.congr_fun Grass.change_one X.val) using 1
    apply congrArg (fun Y=> changeVars Y X.val); ext i j; rw [Matrix.diagonal_mul_diagonal]; simp [Matrix.diagonal_apply,← Complex.ofReal_mul,Matrix.one_apply, mul_comm v u,hr]
lemma bookD (s:Y.Dark): Y.invD s⊆ Y.broad s:=(Matter.range_flags (R:=R) (l:=Q.halo) (T:=T) (b:=radiusB τ) s.1.toLeft).trans ((Y.shellF).lesserP ..)
-- adapt exact LOG and scale
lemma transportTerm (L:ℝ)(V:Grid c)(χ:Chi)(p:Clusters Y.Bright):
   wearK c N L (termP (blocked Y.lightF) (Y.dawnV χ V) p)=termP (blocked Y.lightF) (wearK c N L ∘ Y.dawnV χ V) p:=by
   have he(a:ℝ)(b:EvenA c N):wearK c N L (a • b)=a • wearK c N L b:=map_smul (songT L) ..
   unfold termP; rw [he,he,map_prod]; rfl
lemma totals (U:Grid c)(χ:Chi)(s:Finset (Pipe.Clump S ι)) (fV: Finset (Y.Dark⊕Y.Bright))(hp:Y.registry fV=s):wearK c N a (emergingF Y s χ U)= harvest Y.broad Y.invD Y.lightF (RG.flags (Pressure.temp τ) U) (wearK c N a ∘ duskV Y χ U) (wearK c N a ∘ dawnV Y χ U) fV:=by
    rw [← hp,call_book]; unfold harvest; split
    next _=> rw [map_prod]; exact prod_congr rfl fun i _=> by rcases i with i|i <;> rfl
    exact map_zero _
variable {g:Y.Bright→ℝ}
lemma latest (h:Y.Feasible)(he:0<a) (χ:Chi)(U:Grid c) (hp: Ready Y.lightF (radiusB τ) g c' δ t r)(hx:0≤ c')(hk:∃ v, SumBudget (fun i => ‖token c N a (duskV Y χ U i)‖) v)(hv:∀ i, ‖token c N a (dawnV Y χ U i)‖ ≤ g i) :
   let s:= duskV Y χ U; let X':= dawnV Y χ U; let W:=RG.flags (Pressure.temp τ) U; let Y':= ward Y.broad Y.invD Y.lightF W s X'
   Summable (termP (blocked Y.lightF) X') ∧ Summable Y' ∧ HasSum (fun i=> emergingF Y i χ U) (NormedSpace.exp (scaleU Y.lightF X') * ∑' i,Y' i):=by
   intro s X' W Y'
   let g':= wearK c N a; let t' :=wearK c N a⁻¹; let G:(EvenA c N→L[ℝ]EvenA c N):=songT a; let H:(EvenA c N→L[ℝ]EvenA c N):= songT a⁻¹
   obtain ⟨z,hxj⟩:= hk
   let Y₁:= ward Y.broad Y.invD Y.lightF W (g' ∘ s) (g' ∘ X')
   have hL i:(Y.lightF i).Nonempty:= i.2.1.1
   have hG i: ‖g' (X' i)‖≤ g i:= hv i
   have hn:= bookD Y
   have ha : SumBudget (fun i=>‖(g'∘s) i‖) z:= hxj
   obtain ⟨hZ,hY,hh⟩:= GasP.exact_march _ _ _ W (g'∘s) (g'∘ X') hn hL hp hx hG ha
   let k:= blocked Y.lightF; let Q:= termP k (g' ∘ X'); have hQ := absoluteS k (g'∘X') Y.lightF _ (literal_test _ hL) hL hx (foyer (fun _=>norm_nonneg _) hp hG)
   have ht x:H (g' x)=x:=wit x _ _ (inv_mul_cancel₀ he.ne')
   have hr i: H (Q i)= termP k X' i:=by unfold Q; rw [show termP _ _ i=g' (termP k X' i) from (transportTerm ..).symm, ht]
   have hW : t' ∘ Y₁=Y' :=by
      funext i; change t' (Y₁ i)=_; unfold Y' Y₁ ward; split
      next h=>
        rw [map_prod]; refine prod_congr rfl fun j hj=>?_ ; unfold motto; split
        next h=>
           rw [map_prod]; refine prod_congr rfl fun i hi=>?_; cases i
           next i=> exact ht _
           next i=>
              change t' (NormedSpace.exp (-portion ..)-1)= NormedSpace.exp (-portion ..)-1; rw [map_sub,map_one,NormedSpace.map_exp t' H.continuous,map_neg]; apply congr_arg₂ (·-·) _ rfl; apply congr_arg; apply congr_arg
              unfold portion; change H (∑' x, if seatP Y.lightF x=i then Q x else _) = ∑' x, if seatP Y.lightF x=i then _ else _; rw [H.map_tsum (GasP.somG (k:=Q) hQ.2.1 (p:=seatP Y.lightF) i)]; exact tsum_congr fun j=>by split; exact hr j; exact map_zero H
        exact map_zero t'
      exact map_zero t'
   refine ⟨(H.summable hQ.2.1.of_norm).congr hr,(H.summable hY).congr (fun i=>congr_fun hW i),?_⟩ -- edit
   have hu: Injective Y.registry:= Finset.image_injective Y.bee; refine (hu.hasSum_iff (f:=fun i=> emergingF Y i χ U) (fun i hi=> by_contra (fun hv=> hi (Y.followup i U χ h hv)))).1 ?_
   let F:= harvest Y.broad Y.invD Y.lightF W (g' ∘ s) (g'∘ X')
   have hm : HasSum F (NormedSpace.exp (GasP.scaleU Y.lightF (g'∘X'))*∑' i,Y₁ i):= hh ▸ hZ.hasSum -- dep
   have hh : H ∘ F=(fun i=> emergingF Y i χ U) ∘ Y.registry:=by
      funext i; exact (congr_arg H (totals Y a U χ _ i rfl).symm).trans (ht _)
   rw [← hh]
   have he': H (NormedSpace.exp (scaleU Y.lightF (g'∘X'))*∑' i,Y₁ i)=NormedSpace.exp (scaleU Y.lightF X')* ∑' i,Y' i:=by
      change t' (_*_) = _; rw [map_mul,NormedSpace.map_exp t' H.continuous, show t' (∑' i,Y₁ i)= ∑' i,Y' i from (H.map_tsum hY).trans (tsum_congr (fun i=>congr_fun hW i)), show t' (∑' i,Q i)= GasP.scaleU .. from ?_] -- edit
      exact (H.map_tsum hQ.2.1.of_norm).trans (tsum_congr hr)
   exact he' ▸ H.hasSum hm
end YM.QCD.Loom.Fleet
