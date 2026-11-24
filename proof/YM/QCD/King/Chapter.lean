import YM.QCD.King.Nav
/-! # cost of bright component. Aura cert assembled. -/
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
lemma plenty (X:Coat T F) (h:Y.Famous)(he:Canary su d A)(D:Glass P X V x j W)
 (hz:Y.speaking)(hX:X.x=s)(hp:X.width=o.K) (hx:X.manifest) (hh:8*o.a*Pressure.fiery su s L ≤ d/2)(J:Finset (Bond f))(u:I')(hr:∀ i∈u.toRight, Zest (fun (U: Config su f) t=>Y.works i U (V t)) x j)(w:ℝ):
 let m:=(F.order su).prod X.dice; let K:=songT (c:=c) (N:=N) w; let g t z:=K (playM Y J d u X (V t) z); Meristem g x m j∧ ∀ᶠ y in 𝓝 x,Integrable (g y) m :=by
   intro m K g; let C i a:= rhythm J X (V i) d Q.table u.toLeft R W o.a Q.halo a
   let U (t:F.Slice su ×Air f su) i :=∏ k∈u.toRight,Y.muscle k (vary (X.wrapY t.1) (V i)) (course (X.wrapY t.1) d R.beta t.2 (V i))
   have hV : X.t=Pressure.fiery su s L:=by unfold Coat.t; rw [hX,H.laws.data.funds.length_eq]
   have h₁:0<o.a*X.t:= mul_pos o.large (show 0<X.t from (hX.symm ▸ H.laws.data.room).fiery)
   have hg: Zest U x j:= zing u.toRight _ (fun i hi=> floatingX Y h he X D h₁ (hV ▸ hh) i (hr i hi))
   obtain ⟨M,hB,hF⟩:=(hg.replay K).post
   have hy: ∀ᶠ y in 𝓝 x, Measurable (g y):= by obtain ⟨σ,hs⟩:=D.sails; filter_upwards [nearby X he D.lifts hs] with y hy; exact K.measurable.comp (nectar Y X hz hX hp (V y) he hy u J)
   obtain ⟨T₀,hT,h⟩:= rhythmsM H hX hx hp D he hh u.toLeft J
   refine meritX _ _ ⟨fun u=> T₀ u*M*(1+(1+1):ℝ)^j,(hT.mul_const M).mul_const _,?_⟩ hy
   filter_upwards [h,hF] with y hy hY a; have hS := (brushR (hy a) (hY a)).trim
   exact hS.shimmy (Eventually.of_forall fun i=> show g i a=C i a • K (U a i) from (congr_arg K ((mul_smul ..).symm)).trans (map_smul K _ _))
variable {w':ι→ℝ}{Ω Λ t u pu θ e:ℝ}
def lushR (j:ℕ)(Ω r Λ pu:ℝ):= (1+Ω+2*r)^j*(2+Λ)^j*(1+|pu|)
def stewP (j n:ℕ)(z:ℝ)(K:Piece S ι→ℝ)(v:I'):= z*(∏ i∈v,K i)*(1+worthX Y v)^n
lemma wornP (hw :Guest Y r A Λ t w' e v η χ j)(k' : Kite Ξ A b Ω n pu k θ)(X:Coat T F)(u:I')(V:E → Config su c)(x:E)(he:X.manifest)(h:X.x=s)(hg:X.width=o.K)(hm:X.χ=χ)(hy:(Y.suitcase F).born u)(hQ:(Y.suitcase F).landP X u)(hz:Healthy (Pressure.temp X.x) (Y.fullA u) X.V)(hr:V x=X.V)(hV:Mode V x j v)
 (ha:Y.Famous)(hΩ:Y.speaking)(hS:∀ i∈u.toRight, Zest (fun (U: Config su f) l=>Y.works i U (V l)) x j)(w:ℝ) : let f' i:= Y.lows (podium S su (Y.fullA u) (radiusB s)) u (vary X (V i)); let m:=(F.order su).prod X.dice
 ContDiffAt ℝ (↑j :WithTop ℕ∞) f' x∧ Brush j (stewP Y j (2*j+k) (lushR j Ω r Λ pu) (checkL Ξ w' t w) u) 1 (songT (c:=c) (N:=N) e∘ f') x:=by
    intro f' m; obtain ⟨hd,hV'⟩:= k'.flow F X h hm hg he E V x hr hV
    let I:=edgesM S (Y.fullA u) (radiusB s); let g i:=playM Y I A u X (V i); obtain ⟨hF,hU⟩:=icefall Y ha k'.cap X hd hΩ h hg he k'.speed I u hS
    have hh:f'=ᶠ[𝓝 x] fun i=>∫ z,g i z ∂m:=by filter_upwards [nearby X k'.cap hr hV,hU] with i hi hv'; rw [integral_prod _ hv']; exact billS Y X ha hΩ _ u h hg (H.laws.data.localP F X h hg he).sails.fullC k'.cap hi
    refine ⟨hF.calls.1.congr_of_eventuallyEq hh,?_⟩
    let fK (z:F.Slice su×Air f su) := (X.catastrophe (o.ξ/2) R.beta (blaze u.toLeft)).indicator (fun z'=> facescale I z'^(n*j)) z.2
    obtain ⟨hP,hq⟩:=tails Y Ξ u (n*j) k he hg h hm pu k'.pay
    let K:=songT (c:=c) (N:=N) e; let L':=(1+Ω+2*r)^j*(2+Λ)^j*(1+worthX Y u)^(2*j); let M:= (Real.exp (t*(Y.suitcase F).sizeP u)*(∏i∈u.toRight,w' i))*(∏i∈u.toLeft, Ξ.tag i)*L'
    have hτ: Meristem (fun i z=> K (g i z)) x m j:= (plenty Y X ha k'.cap hd hΩ h hg he k'.speed I u hS e).1 -- annotate
    refine (hτ.buds (fun z=> M*fK z) (hP.const_mul _) zero_le_one ?_ ?_).shimmy ?_
    · rw [integral_const_mul,integral_prod _ (show Integrable fK m from hP)]; unfold fK; dsimp only; rw [integral_const]; simp only [probReal_univ,one_smul]
      have hh:= hw.alive; have hf :0 ≤(1+worthX Y u):=add_nonneg zero_le_one (worthG Y u).2; have ht := (zero_le_one (α:=ℝ)).trans Ξ.active
      have hM:0≤M:=by unfold M; have he:0≤L':=by unfold L'; have h:=k'.extra; positivity; done
                      exact mul_nonneg (mul_nonneg (mul_nonneg (Real.exp_pos _).le (prod_nonneg fun _ _=>hw.cost _)) (prod_nonneg fun _ _=> Ξ.tagged _)) he
      apply (mul_le_mul_of_nonneg_left hq hM).trans; unfold stewP; rw [checkX (F:=F), Ξ.remixes]; apply le_of_eq; unfold M L' lushR; ring
    · apply ae_of_all; intro ⟨v',z⟩
      let Z:= X.wrapY v'; have hp:= k'.flow F Z h hm hg he E V x hr hV |>.2 z
      refine (plex Y Ξ hw u Z I h hg he hm hy hQ hz hV z hp.1 (hp.2.1 I) k'.extra).climb ?_ le_rfl
      by_cases h:z∈ X.catastrophe (o.ξ/2) R.beta (blaze u.toLeft)
      · unfold M fK; rw [Set.indicator_of_mem (show z∈ Z.catastrophe (o.ξ/2) R.beta _ from h),Set.indicator_of_mem h]; exact le_of_eq (by unfold L'; ring)
      unfold fK; rw [Set.indicator_of_notMem (show z∉ Z.catastrophe (o.ξ/2) R.beta _ from h),Set.indicator_of_notMem h,mul_zero]
    filter_upwards [hh,hU] with i hi hv; change K (f' i)=_; rw [show f' i=_ from hi]; exact (K.integral_comp_comm hv).symm
end YM.ConnectedActivityE6.Blaze.King
