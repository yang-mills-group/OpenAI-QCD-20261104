import YM.Poised.Ecume
import YM.Poised.Renew
/-! # choosing pre or post-L expenses together.
   marker Horizon D stepped along variable flights in every banner; precision parameter arbitrary post-length; do not count any part of Post.B as pre here. -/
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
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical
open PhysicalNext.Repeat PhysicalNext.Repeat.Lotus PhysicalNext.Repeat.Sage PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir PhysicalNext.Repeat.Brim
open AnalyticBridge.SectorAffine.Offset Planned.AtomRegular
open QCD.Dust QCD.Brick Pipes Spice MassiveQCD.Lyre Shells Sands MultiNext.SignedSource.Ease
variable {c f L:Side}{S:StepData c f}{T:Tube su S}{P:Teller su}{β τ σ η μ W:ℝ}
variable {R Rx:Rep su f}{O O₁:BudgetPoint}{F:Tree.Forest S.ratio}{Q:Target su P}{o:Target.Order su W}
variable {δ y h t u :ℝ}{q p n m j k α:ℕ}
namespace TrainG
open SourceRead Planned.PrimaryIntegral295.Carrier
-- base ticket. compare: N publication constant.L scale independent. old b count Dd.s
structure Prebit (Q:Target su P)(j k Gh Gd Dd Kq:ℕ)(N₀:Libretto su n)(A₀ A₁ A₂ a b gT:ℝ)(s:ℕ):Prop where
    lore: Diary N₀ P j k Gh Gd Dd A₀ A₁ A₂
    span : 1 ≤ gT
    tax : ∀ L:Side,s ≤ L.val →∀ O:BudgetPoint,O.power=Kq →∀ c f:Side,∀ S:Ratio c f,S.count=L→∀ s s₀ s':ℕ,s ≤ s₀*9^4→ (s':ℝ)≤ preCost (Q.halo+8)+conversion S (Q.halo+8)*s₀ → Real.exp (b*s')*badgeQ N₀ O Gd s ≤ gT*Real.exp (a*s₀)
-- output interval step {
abbrev deckH (p:ℕ)(x:ℝ):ℕ:= voyage p (2*radiusB x) (2*radiusB x)
abbrev mineH (x:ℝ):ℕ:= 2*radiusB x*9^4
abbrev gateH (p:ℕ)(x:ℝ):ℕ:= let t:=2*radiusB x*(4*(2*radiusB x)+2)+2*(2*radiusB x); 1+max (2*(deckH p x+radiusB x)) (10*(t+p))+100*(radiusB x+1) -- syntax
lemma ticketG (p:ℕ)(x:ℝ)(L:Side)(V:BudgetPoint)(q:ℕ) (h: V.B≤2*radiusB x)(ht:q ≤2*radiusB x)(hl:gateH p x ≤ L.val): WindowG L V p q (radiusB x) (deckH p x) x:=by
   let f(B n p:ℕ):= B*(4*n+2)+2*n+p; have he(B N x y:ℕ)(h:B ≤ x)(hx:N ≤ y) : f B N 0≤ f x y 0:=by unfold f; gcongr
   let t:=radiusB x; let n:=f (2*t) (2*t) 0; let m:=f q V.B 0
   have hMm:m ≤n:= he _ _ _ _ ht h; have hM' : f t t 0 ≤ n:= he _ _ _ _ (by omega) (by omega); unfold gateH at hl; dsimp only at hl; change 1+max _ (10*(_+p))+100*_ ≤_ at hl; have hh:n= 2*radiusB x*(4*(2*radiusB x)+2)+2*(2*radiusB x):= rfl  -- add_zero not defeq nat.rec yes
   rw [← hh] at hl
   constructor
   · change 4*m+p ≤ 4*n+p; omega
   · omega
   · change 10*(f t t 0+p)<L.val; omega
   · omega
   change 10*m<L.val; omega
-- cost Mercury
open AnalyticBridge.LocalGaussianLaws
structure Ledger (P₁:Plan j)(Q:Target su P)(J: Patch)(N':Libretto su n)(D:Heir.Record)(o:Target.Order su W) (μ C u v t q a :ℝ)(l k Dc:ℕ)(χ:Chi)(H:TaperHol)(Ht:Hera.Rights su n)(d R' Gh Kq Gn U' D':ℕ)(A₀ A₁ A₂:ℝ)(x:ℝ):Prop where
    vows : Vow P₁ N' Q D U' d D' Kq A₀ A₂ J.L J W μ o C u v t q a l k χ x
    near : Menus P₁ N' D Kq Gh D' U' k A₀ (pup d A₁+pup d A₂) Ht Q J J.L W o μ C u v t q a l χ x (mineH x) (fan J.L (-1/2) x)
    stakes : ∃ τ σ:ℝ,0≤τ∧0<σ∧∀ (c f:Side),LinksT (c:=c) (f:=f) τ σ A₀ H Ht J.L j k R' Kq Dc D' P.bind (deckH R' x) x (relief J.L x)
    funds (P' R:BudgetPoint) : P'.threshold=temp x → R.threshold=fiery su x J.L → R.B=highR J.L x → P'.order=n→ R.order=Gn → P'.power=Kq → R.power=Gh →∀ {c f :Side}(S:StepData c f)(T:Tube su S), S.patch=J → Seam T N'.δ N'.N→ Lift.Booth P S T → 100*(1+radiusB x)≤c.val→ Plays N' D P' R P T x
    holy : 0<radiusB x
    shores : highR J.L x ≤2*radiusB x
    grows : radiusB x+1 ≤ highR J.L x+highR J.L x
    haloP : D.ε ≤1/4
variable (P: Teller su)(Q:Target su P)
set_option maxHeartbeats 890000 in
lemma stable (P₁:Plan j)(k Kq Gh Dd p q i d z m:ℕ)(H:TaperHol)(Hp:Hera.Rights su n)(K a b :ℝ)(ha:0<a)(hb:0 ≤b)(hK:1 ≤ K)(hk:6 ≤ n)(hr:d<n)(hx:n ≤ m)(hμ:0<P.C)(hj:4≤j)(hk':4≤k)(hG: q ≤ P.j-2)(hQ:q ≤ j-2)(hh:q ≤ Gh)(hg:Kq ≤ Gh)(hm:2 ≤ Gh)(he:q ≤Dd)(hy:p ≤ 2*q+2) : ∃ (N:Libretto su n) (A₁ A₂ gT:ℝ)(l:ℕ), Prebit Q j k Gh p Dd Kq N K A₁ A₂ a b gT l ∧ N.δ=P.η∧N.N=P.C ∧ ∀ (L:Side),l≤ L.val →∀ (M:Patch), M.L=L → M.Branches P.bind su →∃ D: Record, ∀ (W μ C u v t q a:ℝ)(l':ℕ)(o:Target.Order su W)(χ: Chi),0<u→0<v→ ∀ᶠ x in atTop,Ledger P₁ Q M N D o μ C u v t q a l' k d χ H Hp p i Gh Kq m z Dd K A₁ A₂ x:=by
    obtain ⟨N,h1,h2,h⟩:= streamsG P P.η P.C n Gh hm P.width hμ.le
    obtain ⟨A₁,A₂,hh'⟩:= comic (N':=N) j k q Gh p Dd K hG hQ hh he hy hK hj hk'; obtain ⟨n1,B,hB,hb'⟩:= beyond N p Kq (Q.halo+8) a b ha hb; obtain ⟨n2,H2⟩:= iron Q P₁ k Dd hj hk' K hK; obtain ⟨n3,H3⟩:= diplomatic (P:=P) P₁ k Dd K hj hk' hK; let y := yarn N.δ N.N; obtain ⟨n4,h4⟩:= eventually_atTop.mp (tendsto_natCast_atTop_atTop.eventually (((tendsto_pow_atTop (show 2≠0 by decide): Tendsto (fun x:ℝ=>x^2) atTop atTop).atTop_div_const (by norm_num : (0:ℝ)<128)).eventually_ge_atTop y) : ∀ᶠ n:ℕ in atTop,y≤(n:ℝ)^2/128)
    refine ⟨N,A₁,A₂,B,n1+n2+n3+n4,⟨hh',hB,fun L h=>hb' L (by omega)⟩,h1,h2,fun L hv M hM hk'=> ?_⟩; let v0:= Kit.slope L^max p 2 /2; have hV:0<v0:=by unfold v0; positivity [Kit.slope_pos L]; --guard
    obtain ⟨D,hξ,hT,Hθ⟩:= songsP M P N hk' (hM.symm ▸ h4 L.val (by omega)) hk m Kq Gh hx hg h 0 (min (1/4) v0) (lt_min (by norm_num) hV); refine ⟨D,fun W μ C u v t q a l o χ hu hv' =>?_⟩
    let s (x:ℝ):=2*radiusB x; have heD:D.ε ≤1/4:=hξ.trans (min_le_left ..); have hD:D.ε≤ Kit.slope M.L^max p 2/2:= hM.symm ▸ hξ.trans (min_le_right ..); have hl:= hξ.trans (min_le_right ..); have ht : 1 ≤ pup p A₁+pup p A₂:=by linarith [pup_pos hh'.warm p,pup_pos hh'.stellar p] -- args
    have hp : Seat M.L 0 (fun x=>(s x:ℝ)):=by unfold s; push_cast; exact Seat.radius.timesL _
    have hX:Seat M.L 0 (fun x=>(mineH x:ℝ)):=by unfold mineH; rw [show (fun x=>(↑(2*radiusB x*9^4:ℕ):ℝ))= fun x=> (s x:ℝ)*(9:ℝ)^4 from funext fun i=> by unfold s; push_cast; ring]; exact hp.times _
    have hi:Seat M.L 0 (fun x=>(deckH i x:ℝ)):=nova i _ M.L hp
    obtain ⟨τ,σ,hτ,hσ,hE⟩:= draft H Hp M.L j k i Kq d Dd P.bind K (zero_le_one.trans hK) hr hj (by assumption) _ hi
    filter_upwards [H2 M.L (by rw [hM]; omega) n p z Kq M N D A₂ (by omega) hh'.stellar hD heD hk' C u v t q a W μ l hv' hu o χ, hE,Hθ,H3 M.L (by rw [hM]; omega) M Q hk' n Kq Gh z N D (pup p A₁+pup p A₂) Hp W o μ C u v t q a l χ mineH hX (by omega) heD hu hv' ht, Work.E01.radiusB_tendsto.eventually_ge_atTop 1,Fees.horizons su M.L 4 (ε:=1) (a:=0) (by norm_num) (by norm_num) (by norm_num :2*(1:ℝ)<3), nails M.L] with x hh0 hE hθ h3 hv hp hN; exact ⟨hh0,h3,⟨τ,σ,hτ,hσ,hE⟩,fun _ _ p1 p2 p3 p4 p5 p6 p7=> (hθ _ _ p1 p2 p3 p4 p5 p6 p7).2, hv,hp.2.1,hN,heD⟩
end TrainG
end YM.Massive.Poised
#print axioms YM.Massive.Poised.TrainG.stable
