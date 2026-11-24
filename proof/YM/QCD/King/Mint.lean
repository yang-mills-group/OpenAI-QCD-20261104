import YM.QCD.King.Arcs
/-! # pricing Permit exactly in playable measure.
 PC consumed after 8×. Does not assume control outside publication. -/
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
variable {Q : YM.ConnectedActivityE6.Target su P}{o :Target.Order su W}{H : Cash W s μ L Q o C T R} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {V : E  →  Config su c} {x : E}
variable {χ:Chi}{ι:Type}{N:ℕ}(Y:Fleet H ι N){K:EvenA c N  →+*EvenA c N}
local notation "I'"=> Pipe.Clump S ι
variable (Ξ : Utopia H j v η r C' χ)
set_option quotPrecheck false
open Pipe
-- require wardrobe v. course for right when all states. adjust speed polynomial ^one extra. T pass value.
def Paint (Y:Fleet H ι N)(z:I')(W':Coat T F)(v:Air f su):=∏ i∈z.toRight,Y.muscle i W' v
structure Guest (_r A:ℝ)(Λ t:ℝ)(g:ι → ℝ)(e:ℝ)(v η:ℝ)(χ: Chi)(k:ℕ) :Prop where
 alive:0 ≤ Λ
 cost:∀ i,0≤g i
 brush :∀ (F:Forest S.ratio)(u:I')(X:Coat T F),X.width=o.K →  X.manifest  →  X.x=s  →  X.χ=χ  →  (Y.suitcase F).born u  →  (Y.suitcase F).landP X u  →  Healthy (Pressure.temp X.x) (Y.fullA u) X.V → ∀ (E:Type)[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E](x:E)(V:E → Config su c)(W:E →  Directions su f)(z:Air f su), Mode V x k v  →  Clutch X z o.a R.beta η x k V W (fun i=> course X A R.beta z (V i))  → 
         Brush k (Real.exp (t*(Y.suitcase F).sizeP u) *(∏i∈u.toRight,g i)) (Λ*(1+worthX Y u)) (fun i=>wearK c N e (Paint Y u (vary X (V i)) (course X A R.beta z (V i)))) x
variable {g: ι → ℝ} {Ω Λ t ζ e:ℝ}
lemma plex (p:Guest Y r A Λ t g e v η χ j) (u:I')(X:Coat T F) (C₁:Finset (Bond f))(h:X.x=s)(hv:X.width=o.K)(hx:X.manifest)(hξ:X.χ=χ)(hr:(Y.suitcase F).born u)(hz:(Y.suitcase F).landP X u)(ht:Healthy (Pressure.temp X.x) (Y.fullA u) X.V)
 (hp:Mode V x j v){Z₁:E → Directions su f}(z:Air f su) (hW:Clutch X z o.a R.beta η x j V Z₁ (fun i=>course X A R.beta z (V i)))(hh: Brush j 1 (Ω*facescale C₁ z^n) (fun i=>scalp C₁ X (V i) R.beta A z) x)(hΩ:0≤Ω):
 let M:= ∏ i∈u.toLeft, Ξ.tag i; let P:= Real.exp (t*(Y.suitcase F).sizeP u)*∏i∈u.toRight,g i
 let W':=(1+Ω+2*r)^j*(2+Λ)^j; let D:=1+worthX Y u
 Brush j ((X.catastrophe (o.ξ/2) R.beta (blaze u.toLeft)).indicator (fun z=> P*M*W'*D^(2*j)*facescale C₁ z^(n*j)) z) 1
     (fun i=>wearK c N e (arts Y C₁ A u X (V i) z)) x:=by
    intro M P W' D
    let f₁ i:= recoil C₁ X (V i) A Q.table u.toLeft R W o.a Q.halo z
    let X'(w: Air f su):= M*(1+Ω+2*r)^j*(1+H.shapeW u.toLeft)^j*facescale C₁ w^(n*j)
    have hC: Healthy (Pressure.temp X.x) (H.unionP u.toLeft) X.V:=Finset.disjoint_of_subset_left ((Y.suitcase F).lesserP u) ht
    have he:Brush j ((X.catastrophe (o.ξ/2) R.beta (blaze u.toLeft)).indicator X' z) 1 f₁ x:=accent Ξ X hp u.toLeft hr.1 hx hC h hξ hv hW hh hΩ
    have ha:= p.brush F u X hv hx h hξ hr hz ht E x V Z₁ z hp hW
    have hx := (brushR he ha).trim
    refine (hx.shimmy (Eventually.of_forall (fun i=> ?_))).climb ?_ le_rfl
    · let Z':=vary X (V i); let w':= course X A R.beta z (V i); change songT e (arts Y _ A u X _ _) = _; rw [show arts Y C₁ A u X (V i) z=f₁ i • Paint Y u Z' w' from (mul_smul ..).symm,map_smul]; rfl

    by_cases h:z∈ X.catastrophe (o.ξ/2) R.beta (blaze u.toLeft)
    swap; · rw [Set.indicator_of_notMem h,Set.indicator_of_notMem h,zero_mul,zero_mul]
    rw [Set.indicator_of_mem h,Set.indicator_of_mem h]
    have hp:1≤D:=le_add_of_nonneg_right (worthG Y u).2
    let D':=1+H.shapeW u.toLeft
    have hD:D'≤D:=add_le_add le_rfl (worthG Y u).1
    let L:=facescale C₁ z
    have hm : 0 ≤ M:=prod_nonneg fun i _=>Ξ.tagged i
    have hp': 0 ≤ L:=zero_le_one.trans (Flux.expenses ..).1
    have h':0≤P:=mul_nonneg (Real.exp_pos _).le (prod_nonneg fun _ _=>p.cost _)
    have hy:=Ξ.active; have hH :0≤ D':= by unfold D'; have hh:= H.positive_volume u.toLeft; positivity
    have hz:0≤Λ:=p.alive; have hv' : 1+(1+Λ*D) ≤(2+Λ)*D:=by linarith
    unfold X'; change M*(1+Ω+2*r)^j*D'^j*L^(n*j)*P*(1+(1+Λ*D))^j≤ P*M*W'*D^(2*j)*L^(n*j)
    calc _ ≤ M*(1+Ω+2*r)^j*D^j*L^(n*j)*P*((2+Λ)*D)^j:=by gcongr
         _ = _ := by unfold W'; rw [mul_pow (2+Λ),show 2*j=j+j by omega,pow_add]; ring
-- supplied by walksW etc
structure FlightP (z:ℕ)(g:ℝ)(e:ℕ) (b x:ℝ)(G:Gauge)(L:Side):Prop where
 exp :∀ (i u t:ℝ), 1 ≤ t  → (0 ≤ i) →  i  ≤  t*ballCost (radiusB x)*(Itinerary.density L:ℝ)  →  u=i*Fintype.card G.ColorIndex  → 
  (1+i+u+u)^z*(1+u*(2*Real.exp (b*(z:ℝ)^2/2)))  ≤ |g| * t^e
lemma tails (u:I')(k l:ℕ)(h:X.manifest)(hx:X.width=o.K)(hp:X.x=s)(hc:X.χ=χ)(t:ℝ)(hs: FlightP (k*2) t l (payE o.eta o.gap o.ample (tubularPrice su L)) s su L) :
 let S':=1+worthX Y u; let I:=edgesM S (Y.fullA u) (radiusB s); let f z:=facescale I z^k; let J:= X.catastrophe (o.ξ/2) R.beta (blaze u.toLeft); Integrable (fun z:F.Slice su×Air _ _=> J.indicator f z.snd) ((F.order su).prod X.dice) ∧ ∫ x,J.indicator f x ∂ X.dice ≤ ((1+|t|)*S'^l)*Ξ.rad^(blaze u.toLeft).card:=by
    intro S' I f J; have hx':1≤ S':= le_add_of_nonneg_right (worthG Y u).2
    have hR:=H.laws.data.localP F X hp hx h; have hM:=globes I hR.sails (k*2); have ht:= (globes I hR.sails k).1; have hQ:MeasurableSet J:= Poll.sounded ..
    have he: (∫ x,f x^2 ∂X.dice) ≤ ((1+|t|)*S'^l)^2 :=by
       unfold f; simp_rw [← pow_mul]; apply hM.2.trans
       let i':ℝ:= I.card; let V:ℝ:= (lensS I su).card
       have hI: i'≤ S'*ballCost (radiusB s)*(Itinerary.density L:ℝ):=by
          have he:= cupLength Y u; rw [H.laws.data.funds.length_eq] at he; apply he.trans; unfold S'; gcongr; linarith
       have hV' : V=i'*Fintype.card su.ColorIndex := by simp [V,i',lensS]
       apply (hs.exp i' V S' hx' (Nat.cast_nonneg _) hI hV').trans; exact (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) (pow_nonneg (zero_le_one.trans hx') _)).trans (le_self_pow₀ (one_le_mul_of_one_le_of_one_le (le_add_of_nonneg_right (abs_nonneg _)) (one_le_pow₀ hx')) (by decide))
    refine ⟨((show Integrable f X.dice from ht).indicator hQ).comp_snd _,divideC _ f ht _ (by positivity) _ hQ ?_ (pow_nonneg Ξ.awake _) ?_ he⟩
    · rw [← pow_mul,Nat.mul_comm,pow_mul]; exact Ξ.ship _ X hp hx hc h _
    unfold f; simp_rw [← pow_mul]; exact hM.1
end YM.ConnectedActivityE6.Blaze.King
