import YM.Poised.Garnish
/-!
# Accounts at all apertures. Covers actually Y^+ when using these. Bound with polynomial factor in length of input support (allows NOTshort in same currency).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Poised
open ConnectedActivityE6 QCD
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets
open Mixed Reserves Trees QCD.Beam QCD.Beam.Pipe QCD.Cove QCD.Leaf Lat Creek Loom Loom.Fleet
open QCD.Leaf QCD.Jets Fj Further.ShellBirth49.Fusing Collide QCD.Jets.Touch
open Kit Fork QCD.Port Flume YM.Next.Free QCD.Leaf Tee QCD.Orbit Quarry Garden Footprint Bay Run QCD.Jets.Sun Pine Grass
open Patron Blaze King March GasP Ursell QCD.Stew Stained
open Sway OrbitG MassiveQCD.Plate MassiveQCD.Apron MassiveQCD.Elevator
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open PhysicalNext.Repeat PhysicalNext.Repeat.Lotus PhysicalNext.Repeat.Sage PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir PhysicalNext.Repeat.Brim
open AnalyticBridge.SectorAffine.Offset Planned.AtomRegular
open QCD.Dust QCD.Brick Pipes Spice MassiveQCD.Lyre Shells Sands MultiNext.SignedSource.Ease
variable {c f L:Side}{S:StepData c f}{T:Tube su S}{P:Teller su}{β τ C μ W:ℝ}
variable {R Rx:Rep su f}{O O₁:BudgetPoint}{F:Tree.Forest S.ratio}{Q:Target su P}{o:Target.Order su W}
variable {δ y:ℝ}{H:Cash W τ μ L Q o C T (trimP T O δ β y)}{ι κ I E J D:Type}{N:ℕ}
variable {n p k d G l:ℕ} {a u r q v σ R z t w m γ α θ η :ℝ}{s:Side}
-- pre-L stipulations

variable {N':Libretto su n}
structure Diary (N':Libretto su n)(P:Teller su)(p k:ℕ)(G₁ G₂ D':ℕ)(K K₁ K₂:ℝ) : Prop where
    warm:1≤ K₁
    stellar:1≤ K₂
    gauge: Fountain.ScrollX N' 0 K₁ G₂ G₁ P
    spirit : ∀ (P':Flight p k)(c f:Side)(h:f.val=c.val*P'.L.val)(O:BudgetPoint)(x y:ℝ)(X:Support f),0<x→0<y→y ≤ K*x→∀ b:Cover,Pipes.Heritage O X b (purseX (wrap f b) D' x) (purseX ((sliceL P' h).parent (wrap f b)) D' y) G₂ (0,flareV (proton P' h)) (Kit.slope P'.L) K₂
variable (Q : Target su P)
lemma comic (p k R:ℕ) (G₁ G₂ D':ℕ) (K:ℝ) (hr:R≤P.j-2) (hs:R≤p-2)(hk:R ≤ G₁)(hG:R ≤ D') (hw:G₂≤2*R+2) (hK:1≤K)(hp:4≤p)(he:4≤k) : ∃ K₁ K₂,Diary N' P p k G₁ G₂ D' K K₁ K₂:=by
    obtain ⟨K₁,h⟩:= Fountain.holders N' 0 P _ _ _ hk hr hw; obtain ⟨K₂,hK',ha⟩:= Pipes.receipt _ _ hG hp he hs _ hK; have hψ: G₂ ≤ 3+2*R:= by omega
    exact ⟨K₁,K₂,h.pos,hK',h,fun P' c f H O x y X h1 h2 h3 b=> ha c f P' H b x y h1 h2 h3 X O G₂ hψ⟩
-- post.V Tape.Priority
structure Vow (P₁:Plan p)(N':Libretto su n)(Q:Target su P)(D:Heir.Record)(U' G₂ D' Kq:ℕ)(K K₂:ℝ)(L:Side)(M:Patch)(W μ:ℝ)(o:Target.Order su W)(C u r t q a:ℝ)(l k:ℕ)(χ:Chi)(x:ℝ): Prop where
    june :∃ A W₁ W₂ σ₁ σ₂ σ₃ σ₄ v:ℝ,(∀ i j:Pipes.Shell,∀ x:su.Color,‖x‖≤1→Through n (yaw i j) x A) ∧ News P L x W Q o μ C n N' D χ Kq W₁ W₂ v M ∧ 0≤ σ₁ ∧ 0≤ σ₂ ∧ 0 ≤ σ₃ ∧
       ((U':ℝ)*(K*2^D'*(σ₂+σ₃))*|W₁|+ |W₂| ≤ Kit.slope L ^G₂) ∧(16*σ₁*K*|W₁|+|W₂| ≤ Kit.slope L ^G₂)∧
       ∀ (B R: BudgetPoint),R.threshold=fiery su x L → B.threshold≤2*R.threshold→ B.power=Kq → R.B=highR L x→∀ (β:ℝ),betaF su x L/2≤β →
       Lute.Plented N' D B R L (Q.halo+5) x (gStep β)∧ R.B ≤2*radiusB x ∧ GramT N' D G₂ A K₂ B R x L ∧ FairT P₁ D N' 2 l L x u r q a v σ₁ σ₄ B ∧ FairT P₁ D N' D' l L x u r q a v σ₂ σ₃ B ∧ ∀ f c:Side,2*(radiusB x+1) < f.val →∀ (P':Flight p k)(h':f.val=c.val*P'.L.val),P'.L=L→∀ (α θ γ ε:ℝ)(E:Offer 1 α θ)(V:Offer 2 γ ε)(m:ℝ), |m| ≤ haloK L x →∀ (Zt:Sun P' c f h' (coneK L r x) t q u a l (pesto P₁ P' h' (trunkM E V (haloK L x) m f))),Consider D' (K*2^D') Zt (radiusB x) R.threshold ∧ Consider 2 (16*K) Zt (radiusB x) R.threshold
lemma iron (P₁:Plan p)(k D':ℕ)(hj:4≤p)(hk:4≤k)(K:ℝ)(hK:1≤K) : ∃ n:ℕ,∀ L:Side,n ≤ L.val → ∀ (n G₂ U' Kq:ℕ)(M:Patch)(N':Libretto su n)(D:Heir.Record)(K₂:ℝ), n≥ 2→1 ≤ K₂ → D.ε ≤ Kit.slope L^max G₂ 2 /2 →D.ε≤1/4→ M.Branches P.bind su → ∀(C u r t q a W μ: ℝ)(l:ℕ),0 < r →0<u→∀ (o : Target.Order su W)(χ:Chi),∀ᶠ x:ℝ in atTop,Vow P₁ N' Q D U' G₂ D' Kq K K₂ L M W μ o C u r t q a l k χ x:=by
    obtain ⟨n1,h1⟩:=diamondsP P₁ 6 D' hj hk (K*2^D') (by positivity); obtain ⟨n2,h2⟩:=diamondsP P₁ 6 2 hj hk (16*K) (by positivity)
    refine ⟨n1+n2,fun L hL n G₂ U' Kq M N' D K₂ hn hκ hE he hM C u r t q a W μ l hr hu o χ=>?_⟩
    obtain ⟨A,hA,hP⟩:= charterY n
    obtain ⟨W₁,W₂,v,hW,hW₂,hv,hY⟩:= Sands.spirit L (Q:=Q) (C:=C) (μ:=μ) (o:=o) N' D χ M hM he hn Kq 0
    obtain ⟨σ₁,σ₄,hσ₁,hσ₄,hx⟩:= trophies P₁ N' D Kq 2 l L u r q a hu hr v hv; obtain ⟨σ₂,σ₃,hσ₂,hσ₃,hX⟩:=trophies P₁ N' D Kq D' l L u r q a hu hr v hv
    let v' := Kit.slope L ^G₂; have hv':0<v':= pow_pos (boxed1 L).1 _
    have hZ₁:=((((hσ₂.add hσ₃).mul_left (K*2^D')|>.mul_left (U':ℝ)).mul hW).below (by norm_num) (v'/2) (half_pos hv')); have hZ₂:=((((hσ₁.mul_left 16).mul_right K).mul hW).below (by norm_num) (v'/2) (half_pos hv'))
    filter_upwards [hZ₁,hZ₂,hY,hx,hX,h1 L (by omega) r u q a hr hu l,h2 L (by omega) r u q a hr hu l,hW₂.below (by norm_num) (v'/2) (half_pos hv'), grading N' D G₂ Kq A K₂ L hE (zero_le_one.trans hA) hκ,plents N' D L (Q.halo+5) Kq (by omega),Fees.horizons su L 4 (ε:=1) (a:=0) (by norm_num) (by norm_num) (by norm_num :2*(1:ℝ)<3)] with x hw₁ hw₂ hy hc₁ hc₂ hh hd hw he ht hg
    obtain ⟨hz1,hz4,hZ⟩:= hc₁; obtain ⟨hz2,hz3,HZ⟩:=hc₂
    constructor; refine ⟨A,W₁ x,W₂ x,σ₁ x,σ₂ x,σ₃ x,σ₄ x,v x,hP,hy,hz1,hz2,hz3,?_,?_,?_⟩
    · rw [abs_mul,abs_of_nonneg (show 0≤(U':ℝ)*(K*2^D'*(σ₂ x +σ₃ x)) by positivity)] at hw₁; linarith only [hw,hw₁, show v'=Kit.slope L^G₂ from rfl] -- linarith transparency
    · rw [abs_mul (16*_*K),abs_of_nonneg (show 0≤16*σ₁ x*K by positivity)] at hw₂; unfold v' at *; linarith only [hw₂,hw]
    intro B R hv h1 hK h2 β hβ; have hp:B.threshold≤2*fiery su x L:= hv ▸ h1
    refine ⟨(ht _ hβ).2 B R hv hK,h2.symm ▸ hg.2.1,he _ _ hv h1 hK,hZ B hp hK,HZ B hp hK,?_⟩
    intro f c hC S H he η A u v E V m hm Zt
    obtain ⟨ψ,hX,hΨ⟩:= hh _ _ hC S H he _ _ _ _ _ _ _ _ hm Zt; obtain ⟨p,hP,hp⟩:= hd _ _ hC S H he _ _ _ _ _ _ _ _ hm Zt
    exact ⟨⟨ψ, hv.symm ▸ hX, he.symm ▸ hΨ⟩,⟨p,hv.symm ▸ hP, he.symm ▸ hp⟩⟩
end YM.Massive.Poised
#print axioms YM.Massive.Poised.iron
