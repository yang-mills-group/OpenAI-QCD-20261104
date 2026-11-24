import YM.QCD.Grove.Dye
import YM.QCD.Grove.Sight
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Trio.Sharp
open Function Filter Lattice RG Pressure Pressure.Testing Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Fare Lapis Metric Further.LogJets Height Roof Input Org Supply Pane Slide
open Push.PriceCompiler ThroughLaunch Height Opera Boulevard
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c C F L:Side}{w b j:ℕ}{B:BudgetPoint}{U V:Config G c}{t d p:ℝ}
section translation
variable (x: Site c)(W:Positions (Uniform.Primary c G))
def shifting : Positions (Uniform.Primary c G):= fun i=> W ((i.1.1+x,i.1.2),i.2)
lemma moved : actual (shifting x W)=translate x (actual W):=by funext i; unfold actual Lattice.translate; rw [represent_link, represent_link]; rfl -- x order
lemma low : ‖shifting x W‖≤ ‖W‖:= (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i=> norm_le_pi_norm W _
abbrev landscape (B: BudgetPoint)(x:Side)(e a:ℝ)(U:Config G x):Prop:=∃ (z: Site x → G.El) (V:Positions (Uniform.Primary x G)), actual V=gauge z U ∧ ‖V‖+2*e<a
lemma carries (U:Config G c)(h:landscape B c d t U) : landscape B c d t (translate x U):=by
    obtain ⟨z,V,hV,hx⟩:=h; refine ⟨fun i=> z (i+x),shifting x V,?_,lt_of_le_of_lt (add_le_add (low ..) le_rfl) hx⟩; rw [moved, hV]; funext i; unfold Lattice.translate Lattice.gauge; simp only; rw [add_right_comm i.1] -- wrong
lemma liner (U:Config G c){H₁:Type*}[NormedAddCommGroup H₁][NormedSpace ℝ H₁](f: Config G c→H₁) (hp:Push.Local.Chart j f (translate x U)): Push.Local.Chart j (f∘ translate x) U:=by
     let M:Directions G c→L[ℝ] Directions G c:= LinearMap.toContinuousLinearMap { toFun:=fun p i=> p (i.1+x,i.2), map_add':=fun i j=>rfl,map_smul':=fun i j=>rfl }
     have hh : Lattice.translate x ∘ increment U=increment (translate x U) ∘ M:=rfl
     unfold Push.Local.Chart; rw [Function.comp_assoc,hh,← Function.comp_assoc]; exact (show ContDiffAt ℝ _ _ (M 0) by rw [map_zero]; exact hp).comp 0 M.contDiff.contDiffAt
-- H₂ unused
end translation
section viewed
variable (P:2*(2*w) ≤ C.val) (o:Site c)(p:Site C)
abbrev delta (w:ℕ) (o:Site c):= o-wrap c (Slide.lev w)
abbrev shapeL (U: Config G c):Config G C:= translate (-delta w p) (Slide.shape (Slide.cognac P) (delta w o) U)
lemma precinct (x:Site C): Slide.sites (Slide.cognac P) (delta w o) x∈ neighbors w o:=by
    let q:=Slide.stage (Slide.cognac P) x; let u:=q- Slide.lev w; have he:q∈crystal (2*w):= Slide.stamp P x; have hg:u∈ Lattice.box w:= by apply (Slide.translate_crystal ..).2; rwa [show u+lev w=q from sub_add_cancel ..]
    apply (neighbors_mem ..).2; rw [show Slide.sites (Slide.cognac P) (delta w o) x=wrap c u+o from (by change wrap c q + (o-wrap c _)=_; unfold u; rw [map_sub]; abel)]; exact Slide.sep u o hg
lemma flare (U:Config G c)(h:Healthy B.threshold (neighbors w o) U): flags B.threshold (shapeL P o p U)=∅:=by unfold shapeL; rw [← pull_one]; exact Pane.tranquility _ (allFlag (cognac P) _ _ _ (precinct P o) _ B.threshold_pos.le h) _ _
lemma hearth (U:Config G c):Agrees (Lattice.box w) (expandAt p (shapeL P o p U)) (expandAt o U):=by
    let A:= cognac P; let a:= lev w; rintro ⟨i,j⟩ hi ht
    have hp:i+a∈crystal (2*w):=(Slide.translate_crystal ..).1 hi
    have hk:i+a+step j∈crystal (2*w):=by rw [add_right_comm]; exact (Slide.translate_crystal ..).1 ht
    have hh (p:Site C):wrap C i + p+ -delta w p= wrap C (i+a):= by rw [map_add]; unfold delta a; abel
    change Slide.shape A (delta w o) U (wrap C i+p+ -delta w p,j)=U (wrap c i+o,j); rw [hh,Slide.vested P (i+a) hp j hk,map_add]; congr 2; unfold delta a; abel
lemma rests (U:Config G c)(F: Config G C→ℝ) (hp:Push.Local.Chart B.order F (shapeL P o p U)) (ht:∀ l: List (Directions G C), l.length ≤ B.order→(∀ i∈l,‖i‖≤ B.threshold)→‖leftDerivs F l (shapeL P o p U)‖ ≤ t) (l:List (Directions G c))(hk:l.length ≤ B.order)(hL:∀ i∈l,B.dirBound (delta w o) i) : ‖leftDerivs (F∘shapeL P o p) l U‖ ≤ 2^B.order*((1+(2*w:ℕ):ℝ)^(B.power*B.order))*t:=by -- anchor difference must change to o
    let V:=Slide.shape (Slide.cognac P) (delta w o) U; let x := -(delta w p); let T:= translate (K:=G.El) x
    apply Slide.stalled  (q:=t) (cognac P) (delta w o) (F ∘ T) (village P _) l U hk hL (liner _ V F hp)
    intro L h₁ h₂
    let g (w: Directions G C) : Directions G C:= fun i=> w (i.1+x,i.2)
    have hh (L:List (Directions G C))(U:Config G C) : leftDerivs (F ∘ T) L U=leftDerivs F (L.map g) (T U):=by induction L generalizing U with
                                                                                                                 | nil=>rfl
                                                                                                                 | cons i l ih=> simp only [List.map_cons,leftDerivs,ih]; rfl -- congr definitional
    rw [hh]; refine ht _ (by simpa) (fun i hi=> ?_); obtain ⟨y,hy,rfl⟩:=List.mem_map.mp hi; exact (pi_norm_le_iff_of_nonneg B.threshold_pos.le).2 fun i=> (norm_le_pi_norm y _).trans (h₂ _ hy)
end viewed
end YM.PhysicalNext.Repeat.Trio.Sharp
