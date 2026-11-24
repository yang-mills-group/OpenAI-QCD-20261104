import YM.QCD.King.Acres
/-! # dressed vector left derivatives at the threatened equality. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze.King
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation Golden
open QCD QCD.Beam QCD.Loom Fleet QCD.Patron QCD.Cove PhysicalNext.Repeat.Greenbelt
open Push.AbsoluteSums Mixed Trees Reserves
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical PhysicalNext.Repeat.Greenbelt
variable {c f L : Side} {S : StepData c f} {T : Tube su S} {F : Forest S.ratio} {P : Teller su}
variable {j n l k : ℕ} {R : Rep su f} {X : Coat T F} {I : Finset (Tubular f su)} {η r q a W d C' A b s μ C v B: ℝ}
variable {Q : YM.ConnectedActivityE6.Target su P}{o :Target.Order su W}{H : Cash W s μ L Q o C T R} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {V : E → Config su c} {x : E}
variable {χ:Chi}{ι:Type}{N:ℕ}(Y:Fleet H ι N){K:EvenA c N →+*EvenA c N}
local notation "I'"=> Pipe.Clump S ι
variable (Ξ : Utopia H j v η r C' χ)
set_option quotPrecheck false
open Pipe
open March Territory QCD.GasP Gas Ursell QCD.Stew
variable {w:ℕ}{w':ι → ℝ}{Ω Λ t u pu θ e δ r':ℝ}
variable {C_:RegularAddress c}{U₀:Config su c}{p:BudgetPoint}{Z':Config su c → EvenA c N}
-- `Occupation`: need not assume differentiability in a space. price B
structure Money (g : Config su c → EvenA c N) (V:Config su c)(v B w:ℝ)(j:ℕ):Prop where
  content : ∀ (E:Type)[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E](U:E → Config su c)(x:E), U x=V → Mode U x j v → ContDiffAt ℝ (↑j : WithTop ℕ∞) (g ∘ U) x ∧ Brush j B 1 (songT w ∘ g ∘ U) x
section rent
lemma Canvas (g: Config su c → EvenA c N)(V:Config su c)(h:Money g V v B e j)(hv:0<v): Push.Local.Chart j g V := by
  obtain ⟨u,hu,hg⟩:= expCost su j 1
  let a:=1+j.factorial*u; have ha : 0<a := by unfold a; positivity
  let d:= v/(2*a); have hd : 0<d:= by unfold d; positivity
  let L := d • ContinuousLinearMap.id ℝ (Directions su c)
  have hL : ‖L‖ ≤ 1*d := by unfold L; rw [norm_smul,Real.norm_of_nonneg hd.le]; exact (mul_le_of_le_one_right hd.le ContinuousLinearMap.norm_id_le).trans_eq (one_mul d).symm
  have hh := fromLogL L (x:=0) (linearB L (u:=1) (d:=d) (by simp) hL hd.le) 1 zero_lt_one hg (by intro i; simp only [map_zero, Pi.zero_apply]; simp) V
  have he : (1+(j.factorial:ℝ)*u)*((1+1)*d)=v := by change a*_ =_; unfold d; field_simp; ring
  rw [he] at hh
  let f Z := g (increment V (L Z))
  have hp : ContDiffAt ℝ (↑j) f 0 := (h.content _ (fun a=> increment V (L a)) 0 (by rw [map_zero]; exact Work.G07.at_zero_increment V) hh).1
  let M := d⁻¹ • ContinuousLinearMap.id ℝ (Directions su c)
  unfold Push.Local.Chart; rw [show g∘increment V=f ∘ M from funext fun _=> by simp [f,M,L,smul_smul,hd.ne']]; exact ((show ContDiffAt ℝ (↑j) f (M 0) from by rw [map_zero]; exact hp)).comp (0:Directions su c) (f:=M) M.contDiff.contDiffAt
lemma gatedL (h:∀ U,Gated C_.support (Z' U))(l:List (Directions su c)) :∀ V,Gated C_.support (leftDerivs Z' l V):=by
   induction l with
   | nil=>exact h
   | cons a l ih=>
    intro V; obtain ⟨U,hU⟩:=solvent (N:=N) C_.support; let f(x:ℝ):=leftDerivs Z' l (increment V (x • a)); rw [hU]; change deriv f 0 ∈ U
    have hp i: f i∈ U:= (hU _).1 (ih _)
    by_cases he:DifferentiableAt ℝ f 0
    swap; · rw [deriv_zero_of_not_differentiableAt he]; exact U.zero_mem
    have hx:= hasDerivAt_iff_tendsto_slope.1 he.hasDerivAt
    apply IsClosed.mem_of_tendsto (Submodule.closed_of_finiteDimensional U) hx
    exact Eventually.of_forall fun i=> show slope f 0 i ∈ U from U.smul_mem _ (U.sub_mem (hp i) (hp 0))
noncomputable def wag (A: Support c)(B:ℕ):ℕ:=coverNumber B A*(4*B+2)+2*B
lemma vistaQ (hp:p.order=j)(he:0<v)(ha:0<e)(hm:Money Z' U₀ v B e j)(hf:LocalOn C_.support Z')(hX:∀ i,Gated C_.support (Z' i))(hk:Sailor su p.threshold Λ j)(hz:0 ≤ Λ)(hv:j*Λ ≤ v)(l:List (Directions su c))(hl:l.length ≤ j)(hg:∀ i∈l,p.dirBound C_.site i): Sen C_.site e (leftDerivs Z' l U₀) ≤ (1+(wag C_.support p.B:ℝ))^(2+p.power*j)*B:=by
    let i:=C_.site; let W':=C_.support; let t:=wag W' p.B
    have ht:∀ x∈ W',separation x i ≤ t:=fun x hx=> Corona.extent W' p.B hx C_.anchor
    let y:=1+(t:ℝ); have hy:1≤y:=le_add_of_nonneg_right (Nat.cast_nonneg _)
    apply (senCamp C_.support ht (leftDerivs Z' l U₀) ha (gatedL hX l _)).trans; rw [pow_add,mul_assoc]; refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
    let w:=songT e (c:=c) (N:=N); let u:= w (leftDerivs Z' l U₀)
    obtain ⟨g,he',hh'⟩:=exists_dual_vector'' ℝ u
    let f:=g.comp w; let F:=f ∘ Z'; have hh:g u=leftDerivs F l U₀:= (Push.Local.left_linear f l (Canvas Z' U₀ hm he) hl).symm
    have hF:Ore U₀ F v B j:=by
       intro E _ _ _ Y x hy h; have ht:= ((hm.content _ Y x hy h).2.report g he'); rw [one_mul] at ht; exact ht
    change ‖u‖ ≤ y^(p.power*j)*B; have hT:g u=‖u‖:=hh'
    have hv': ‖g u‖= ‖u‖:=by rw [hT,Real.norm_of_nonneg (norm_nonneg _)]
    rw [← hv',hh]; exact costsD (fun a b hh=>congr_arg f (hf _ _ hh)) hk hz C_.site B hv hF (fun i hi=> add_le_add le_rfl (Nat.cast_le.mpr (ht _ hi))) hy l (by omega) hg
end rent
variable (K':Kite Ξ A b Ω n pu k θ) (hw:Guest Y r A t u w' e v η χ j) (hp:Y.Famous)(hx:Y.speaking)
variable (Z:Clusters Y.Bright → RegularAddress c)
include K' hw hp hx
lemma gold (hg:Territory.Gate Y)(hA:∀ i,(Z i).support=seatP Y.lightF i)(i:Clusters Y.Bright)(hQ:p.order=j)(he:0<v)(ha:0<e)(hk: Sailor su p.threshold Λ j)(hM:p.threshold=Pressure.temp s)(hz:0≤ Λ)(hv:j*Λ ≤ v) (w:ℝ)(hn:Peace Y)
 (hP:∀ (E:Type)[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E](V:E → Config su c)(x:E), Mode V x j v → ∀ i,Zest (fun u y=> Y.works i u (V y)) x j):
 let a:ℝ→ℝ:=id; let F:=crude Y χ Z; let X:=seatP Y.lightF i; let K p:= stewP Y j (2*j+k) (lushR j Ω r t pu) (checkL Ξ w' u w) (p:Y.Bright).val; let B':= badgeD Y j i K
 Woven (Z i).site X p e (F.view i) ((1+(wag X p.B:ℝ))^(2+p.power*j)*B'):=by
   intro a G C₀ r' B; have he' (U:Config su c)(h:Healthy p.threshold (Z i).support U):Money (G.view i) U v B e j:=by
      constructor; intro E _ _ _ V x hE he; exact King.survey Y Ξ K' hw hp hx i w he (hE.symm ▸ hM ▸ hA i ▸ h) (hP _ V x he) Z hn
   have hG:G.Gather:=plumE Y Z χ hA hp hg hx
   have hh:C₀=(Z i).support:=(hA _).symm
   rw [hh]; refine ⟨hG.sees i,hG.role i,?_,?_,hG.reads i,?_⟩
   · intro U h; rw [hQ]; exact Canvas _ U (he' _ h) he
   · intro U h l hV hp; rw [hQ] at hV; exact vistaQ (C_:=Z i) hQ he ha (he' _ h) (hG.sees _) (hG.role _) hk hz hv l hV hp
   apply mul_nonneg (by positivity); have hh:= he' (1:Config su c) (AnalyticBridge.VerifiedReset.flat_ok ..)
   exact (hh.content ℝ (fun _=>1) 0 rfl (show Mode (fun _:ℝ=>1) 0 j v from ⟨he.le, fun _=> a_oneB _ _ he.le⟩)).2.nonneg
end YM.ConnectedActivityE6.Blaze.King
