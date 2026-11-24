import YM.QCD.Octave.Fields
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Octave
open Function Filter Set Metric MeasureTheory Lattice Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure Presented
open PhysicalNext.Repeat Lapis Sienna Lantern Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat
open AbsoluteSums Fare Tidings Token Shield Beam Cove Golden NormedSpace
open scoped Topology ENNReal ContDiff BigOperators Classical
open Lat YM.Next.Free Reggae
open Jets.Touch Port Kit Run Stew Bay Strut Leaf Tee Flume Garden Kings Orbit LeafM
open scoped Matrix.Norms.L2Operator
open Revolve
open Loom Fleet
open AtomF
open Loom Fleet AtomF Oasis
variable {j k n l N:ℕ}{M p a v d Z θ s r p' s' w u γ τ ϑ:ℝ}{K:KernelChoices} {m R y:ℝ→ℝ}
local notation "W"=>glimB
-- y:C budget at positive elem. use crown Norm opt
lemma halo_bound {S:Side}(h:0<p):∀ᶠ x in atTop, wink S x≤ p:=by
    filter_upwards [(Rate.power (a:=-((1:ℝ)/2)) (G:=su) (L:=S) |>.below (by norm_num) p h) ] with i h using (le_abs_self _).trans h
lemma lampL (L:Side)(B:ℕ)(N:ℕ)(P:Plan j)(a b u p r d:ℝ)(hw:Bolt su L y)(hm:Rate su L 0 m)(ha:0<a)(hb:0<b)(hθ:0<θ)(hκ:0<r)(hϑ:0< ϑ)(hs:w>0)(hk:2≤B):∃ A Z X:ℝ→ℝ, Seat L (θ*2) A∧ Seat L (θ*2) Z ∧ Seat L (θ*2) X ∧ ∀ᶠ t:ℝ in atTop,∀ (c f:Side)(F':Flight j k)(e: f.val=c.val*F'.L.val)(S:StepData c f)(F:Forest S.ratio)(Y:Tube su S), Quilt Y F (y t) → F'.L=L→ ∀ (J:Offer 1 a u)(T:Offer 2 b p)(W':ℕ→ Atom su 2), Extra.Iteration.Charged W' r d→Extra.Iteration.SymmetricAtoms W'→∀ b', |b'|≤wink L t→
      let K:=park F' e P J T (haloK L t) b'
      let U:=tonic e K W' N (highW L w θ t); 0 ≤ m t → Continuous U ∧ (∀ i, ‖U i‖ ≤ X t) ∧ TellerX (U ∘ projection F) (spanV (fan L ϑ t) (m t)) (eaves su L t) (A t) (Z t) B :=by
    let v:= highW L w θ; have hv: Seat L θ v:= Seat.timesL Seat.keeps w
    obtain ⟨c,hc,hπ⟩:= highGeom N; let O i:= c*y i
    have hy: Seat L 0 y:=fun r hr=> hw.listens hr; have hO:Seat L 0 O:=hy.timesL _
    obtain ⟨ν,xz,Fq,D,A,b',i,i',hν,hp,hz,hA,H⟩:=revenueT (k:=k) ha hb P 0 u d p r N L hκ
    let g t:=coneK L ν t
    choose C hC using paint_supply su
    let J t j:= gross (C j) (g t) Fq A (y t) (O t) (v t) j N; let J' t j:=gross (C j) (ν*b'^2) Fq A (y t) (O t) (v t) j N
    have hh:= roofF' (ν*b'^2) 2 N (C 2) Fq A hy hO hv hθ
    let T t:=fan L ϑ t; let U t:=eaves su L t
    let q t:=spanV (T t) |m t| * U t; have he: Rate su L vow q:= ((Rate.add (((Rate.const 2).add (Brim.absolut hm))) (Seat.keeps (L:=L) (a:=ϑ)|>.ruled)).mul (edge su L)|>.weaken (by linarith))
    have h'q:∀ᶠ i in atTop,0 < q i := (Delay.shift_pos su L).mono fun i hi=> mul_pos (by unfold spanV; have h:0 < T i:=fan_pos ..; positivity) (Real.rpow_pos_of_pos hi _)
    refine ⟨(fun i=> J' i 2),fun i=>J' i 2+1,(fun i=>fundsX (y i) (O i) (v i) A Fq N),hh,hh.comb ((Seat.numbers 1).above (by positivity)),mansF N A Fq hy hO hv hθ,?_⟩
    filter_upwards [skyCost hν hθ hy hO hv he h'q C N B Fq A, halo_bound (S:=L) hp,kentucky L hp,h'q] with t ht ht' hi hi' c f F' e S F Y hG hF J₀ T' W' hV hW m₀ hM V W₀ hmu
    obtain ⟨h,hk'⟩:= H J₀ T' W' hV hW c f F' e m₀ _ hF hi.1 hi.2.1 (hM.trans ht') -- SOIL shadow h
    let P':= park F' e P J₀ T' b' m₀; obtain ⟨hf',he'⟩:= H J₀ T' W' hV hW c f F' e m₀ b' hF hp le_rfl (hM.trans ht')
    have hu: (Fintype.card (Modes c N):ℝ) ≤ O t := (hπ c).trans_le (mul_le_mul_of_nonneg_left hG.primary hc)
    have hv :0 < v t:= mul_pos hs (fan_pos ..); have hy' :0<g t:=mul_pos hν (pow_pos hi.1 _); have ht'': 0<ν*b'^2:=mul_pos hν (pow_pos hp _)
    refine ⟨portage e _ _ h hk' hy', fun U'=>musterX e _ _ h hk' hy' le_rfl hv hA hG.finalP hu _,?_⟩
    have hp' x (hx : ‖x‖<q t) j: Brush j (J t j) 1 (W₀ ∘ projection F) x:= conscientious F e _ _ h hk' hy' le_rfl hv hA (hC j) hG.finalP hu (hx.le.trans ht.1)
    let g:= W₀ ∘ projection F
    have hh := conscientious (O:=F') F e _ _ hf' he' ht'' le_rfl hv hA (hC 2) hG.finalP hu (x:=0) (by simp)
    have hx := muted (hyphen F F' e P J₀ T' W' ha hb hy' ht'' h hf' hi.1 hi.2.2 hp hz hk' (s:=v t) (N:=N)); change ∀ i≤2, iteratedFDeriv ℝ i g _=_ at hx
    have hW : ‖fderiv ℝ g 0‖ ≤ J' t 2:= by rw [← norm_iteratedFDeriv_one,hx 1 (by omega)]; exact (Brush.offer.mp hh).2 _ (by omega)
    have hx' :normJ 2 g 0≤ J' t 2:=by unfold normJ; rw [hx 2 le_rfl]; exact (Brush.offer.mp hh).2 _ le_rfl
    have htQ : spanV (fan L ϑ t) (m t)* U t=q t:= by unfold q; rw [abs_of_nonneg hmu]
    refine ⟨fderiv ℝ g 0,hW,?_⟩; intro x hx; rw [show spanV _ _* eaves su L t=q t from htQ]
    have hz':0 ≤ J' t 2:=hh.nonneg
    refine hour hk hi' (T:=g) (by positivity) (fun i hi=> (hp' i hi B).smooth) (fun j he hj x hy=> ?_) x hx
    rcases eq_or_lt_of_le he with hj'|h'
    · subst j; exact mul_le_mul_of_nonneg_right (pants hi' (fun i hi=> hp' i hi 3) ht.2.1 hy hx') (by positivity)
    have hh':= hp' x hy j; exact ((mul_le_mul_of_nonneg_right ((Brush.offer.1 hh').2 _ le_rfl) (by positivity : 0 ≤ q t^j)).trans (ht.2.2 _ h' hj)).trans (le_mul_of_one_le_left (by positivity) (by linarith))
end YM.QCD.Octave
#print axioms YM.QCD.Octave.lampL
