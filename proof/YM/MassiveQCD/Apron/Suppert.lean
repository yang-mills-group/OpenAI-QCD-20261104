import YM.MassiveQCD.Apron.Groves
/-! # budgeting extended grading marker apertures. Purchasing SAME old & new proofs. Adapted from QCD/Calm/Surge. Upper Path support requires later Level-wise alignment; the hypothesis on a Plateau c not arbitrary Tuple. No positivity assumption anywhere in the Tape. Real Haar-G gauge/Grassmann.Voice. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Loom
open ConnectedActivityE6
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets
open Mixed Reserves Trees Beam Beam.Pipe Cove Leaf Lat Creek
open Leaf Jets Fj Further.ShellBirth49.Fusing Collide Jets.Touch Fleet
open Kit Fork Port Flume YM.Next.Free Leaf Tee Orbit Quarry Garden Footprint Bay Run Jets.Sun Pine Grass
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical
variable {c f s:Side}{P:Teller su}{δ β b τ μ W C d':ℝ}{Q:Target su P}{o :Target.Order su W}{R:BudgetPoint}{N m l n i j k:ℕ}
variable {η p h z a a' t v V u u' q θ w₁:ℝ}{G₁: Plan j}{G₂:Plan k}
variable (L:Flight j k)(d:f.val=c.val*L.L.val)(O:KernelChoices)
variable {T : Tube su (Flight.visit L O d)} {W' :ℕ→Atom su 2} {P':Plan k}{X : St f}
local notation "S"=> Flight.visit L O d
variable {t0 a0 D U' A b' k0 θ' ε R' X' iP ip α y q' Ω:ℝ}
open Kings Blaze Vine King
-- station program pre output, BEFORE actual β shooting. ensure power statement θ ratio Ω note parameter bug dilation `η=u?`${} inspect.
open MassiveQCD.Apron
set_option maxHeartbeats 1300000 in
lemma summer_ext {s:Side}(hc:CardT s N 38 36 C θ θ G₁ G₂ a b A D t θ p t0 Q.relative k0 Ω R' X' Q.relative i m z y q' q) (hv:0<θ)(hs:θ<1/8)(he:1 ≤k0)
 (_u X0 μ W:ℝ) (hl:0<μ)(hp:0≤X0)(o:Target.Order su W) (v':ℝ → ℝ)(hV: Rate su s (-(1/2)) v')(pA:ℝ)(hQ:0<pA)(hR:pA<p)(Dq:ℝ)(hq:∀ (c f: Side)(G: Ratio c f), G.count=s → reserve pA Q.relative (conversion G 36) Dq) (χ:Chi)(Wq:ℕ)(r b1:ℝ)(N₁:ℕ)(hr:0<r)(hb1:0<b1): ∀ᶠ x in atTop,
     let _B:=radiusB x; let I:=haloK s x; let v:=coneK s z x; let Z:=highW s k0 θ x; let t':=fiery su x s
     ∀ (c f : Side)(L: Flight j k)(H:f.val=c.val*L.L.val)(K:KernelChoices)(T:Tube su (Flight.visit L K H)),L.L=s→ 2*(radiusB x+1)<f.val →∀ (O:Garden.Offer 1 a A)(D': Garden.Offer 2 b D)(m':ℝ)(W0:ℕ→Atom su 2),|m'| ≤ wink s x → Extra.Iteration.Charged W0 t Ω→ Extra.Iteration.SymmetricAtoms W0→
     let p':=park L H G₁ O D' I m'; Nonempty (Sun L c f H v y q' p q i p')∧Nonempty (Swathe L H p' W0 G₂ y v p X' R' m)∧
     ∀ (G:Sun L c f H v y q' p q i p')(V:Swathe L H p' W0 G₂ y v p X' R' m) (rP:BudgetPoint)(β b0:ℝ),
     let δ:=lowK s x P.top.supportExponent
     let V':= trimP T rP δ β b0
     ∀ (Y:Cash W x μ L.L Q o X0 T V'),∀ (Xg: Land c (Site c) (Site c))(Zg:Pays c (Site c) (Site c)), Run.Pack id id r ((Q.relative*(10*preCost 37)+3)+1) N₁ (wood G₂ 0 L.land) b1 Xg Zg→ Villa.Torch Xg→∀ {J E:Type}[Countable J][Countable E] (p:Rise f N E J),∀ dV dX,Cents p dV dX (fan s θ x) t' → Fill p dV dX t0 t0 (taxK s x 1) 1 (chip s x) (highR s x) → p.Wave t'→ p.Reframe →∀ F:Tree.Forest (Flight.visit L K H).ratio,∃ Y' u' aH θ' l,0<u' ∧ 0<v ∧ (River L H K p Y G V F θ Z Xg Y' u' aH θ' l ∧ let V₀:= tableau L H K p Y G V Xg
       ∀ (C₁ b₁ e q r A Θ B:ℝ) (n k :ℕ)(Ξ: Silica.Utopia Y Wq (v' x) b₁ e C₁ χ), Kite Ξ A r Θ n B k q → 0 ≤ v' x → ∃ w, Guest V₀ e A (royal q) (shiftCost L.L x (romp L.L)) w Z (v' x) b₁ χ Wq ∧ Ac.Hit V₀.ground (radiusB x) (fun i=> glazeL L.L x i*w i) Q.relative (δCharge L.L θ x)) ∧ ∀ (T:Type)[Fintype T](μ:T→Bool) (Yn: MassiveQCD.Stitch.Tablet p T)(Y₂:T→Site f), Yn.Wave rP.threshold μ Y₂ → Yn.Coins dV dX (fan s θ x) t' →
       let V₀:= MassiveQCD.Apron.vantage L H K Y G V Xg Yn Y₂ Z; 1 ≤ Z ∧ (∀ U: Grid f, Yn.Staid rP.threshold U) ∧ V₀.gator ∧ V₀.Famous ∧ V₀.Feasible ∧ Grove.Shed L H K Y F V₀ Z θ ∧ 
       ∀ (C₁ b₁ e q r A Θ B:ℝ) (n k :ℕ)(Ξ: Silica.Utopia Y Wq (v' x) b₁ e C₁ χ), Kite Ξ A r Θ n B k q → 0 ≤ v' x → ∃ w, Guest V₀ e A (royal q) (shiftCost L.L x (romp L.L)) w Z (v' x) b₁ χ Wq ∧ Ac.Hit V₀.ground (radiusB x) (fun i=> glazeL L.L x i*w i) Q.relative (δCharge L.L θ x) :=by -- existential sums under Ω positivity implicit. shadow arg. enlarge proposition
   let d:= Q.relative * (10* preCost 37)+3; have he' : reserve d Q.relative (10*preCost 37) 1:=by
      have ht:= Q.bound; have hv:= Q.usable; have ht':= Q.pos
      exact ⟨by unfold Target.relative; linarith,zero_lt_one,by unfold d; linarith⟩
   have hd':0 ≤ d:=by
     unfold d; have hA:=he'.1; have hm:0 ≤ preCost 37:=by unfold preCost; positivity
     positivity

   obtain ⟨f₀,hf,hF⟩:= hammock P s o.a o.large
   have hy':0<p:=hc.grow.wolf
   have hw : ∀ᶠ x in atTop,1 ≤ highW s k0 θ x:=((Jets.Touch.Seat.your s).eventually_ge_atTop 1).mono fun i hi=>one_le_mul_of_one_le_of_one_le he (Real.one_le_rpow hi hv.le)
   have hhP:0<2*o.a:=mul_pos (by norm_num) o.large
   obtain ⟨M₂,hM₂,hX₂⟩:= hammock P s (2*o.a) hhP
   filter_upwards [hc.permit,hc.grow.pays,guests Q s (μ:=μ) hl hv hp,forwardG hp (p:=d+1) (by linarith) hv hs he s N N₁ hr hb1.le hf P Q W o μ hd' he', hF,dipK s P.top.supportExponent,hw, Work.E01.radiusB_tendsto.eventually_ge_atTop 1, insoleP G₁ P s X' k0 z R' θ p o.a q' q y 0 i m N a b A D q 0 G₂ hf o.large hy' hc.grow.orbit (by linarith), (Jets.Touch.Seat.your s).eventually_ge_atTop 1, hX₂, paysLong P s j k 0 36 m N 0 k0 Q.relative X' R' p θ Dq pA 0 hQ hR, buyS Q k0 r θ d (d+1) N Wq hr hv hs hd' (by linarith) s (V:=v') 0 he b1 N₁ μ hM₂ hV he' o, Delay.shift_pos su s,insoleP G₁ P s X' k0 z R' θ p (2*o.a) q' q y 0 i m N a b A D q 0 G₂ hM₂ hhP hy' hc.grow.orbit (by linarith), hw] with x hp' hA hx hG hS hB ht hn hi hkS hkF hj hvG hz hi₁ hXV -- edith hA params
   intro I v Z t' c f L H K TD hL hs0 O Ds m' W₀ hM hW hW' fQ
   subst s
   obtain ⟨hr0,hh0,hk0,hM0,hQ⟩:= hp' f c hs0 L H rfl O Ds m' hM; obtain ⟨hQ,hfQ⟩:=hQ W₀ hW hW'
   refine ⟨hM0,hQ,fun G V R β b₀=>?_⟩
   intro δ Y' YH
   let S₁:=Flight.visit L K H
   intro Xg Zg hxg hτg J E _ _ P₀ dV dX H₁ H₂ H₃ H₄ F
   obtain ⟨hz,hZ⟩:= hfQ V
   obtain ⟨hg,hg'⟩:= hG c f S₁ TD Y' rfl F (wood G₂ 0 L.land) _ _ hxg YH hS
   let XU:= VarnC YH V N
   have hT: S₁.ratio=sliceL L H:=rfl
   have hα: β=Y'.beta:=rfl
   let B:=radiusB x
   have hJ := YH.laws.intake
   have hJC:= YH.laws.data
   have hv' : Fleet.Theft XU F (fun i=>siteH i S₁.ratio) (fun i=>Real.exp 1*Port.shells V N B Z (coreRate L.L x) i) Z (fan L.L (1/4) x) _ (18*B) _ := metered YH V hT hz fun Y he he' hy i hh hg w hN=>by
     let Uv:= Y.liftA β w
     exact hi c f L H rfl O Ds m' hM hh0 W₀ V S₁ TD F Y rfl hJC.room hT he hy hS i hh Uv _ (marks i S₁.ratio B) hN hg
   have hR: R.threshold=fiery su x L.L:= hJ.received.temp
   let Xq:= G.equip N B
   let Tq:= roof Xq P₀ 30 B
   have he:= roofs Xq P₀ 30 B le_rfl (show 0<B from hn)
   obtain ⟨hf',hi',hw',ht'⟩:=((hA.2.2 f c hs0 O Ds m' L H rfl hr0).2 G P₀ dV dX Tq H₁ H₂ he.1 he.2)
   have HH : P₀.Wave R.threshold:=hR.symm ▸ H₃; have HI : Cents P₀ dV dX (fan L.L θ x) R.threshold:=hR.symm ▸ H₁
   have hP := homeP YH Xq P₀ Tq (hR.symm ▸ hf') HI HH hB.1 rfl ht (fun U' g he s=>fowl YH P₀ L H G U' g he B H₄ s) -- args
   let Xv:= deckHue YH Xq P₀ Tq
   have hx:= hx β (show betaF su x L.L/2 ≤β from hJ.window.1)
   have hf:(tableau L H K P₀ YH G V Xg).Famous:= jungle Xv _ hP (jungle XU _ (bridgeC YH V hT hz.growth) (sailors YH hxg hr))
   have hb:= shiner (u:=fan L.L (1/4) x) (F:=F) (i:=0) (n:=0) YH Xq P₀ Tq (hR.symm ▸ hf') HI HH hB.1 (fun _=>0) (fan_pos ..).le
   have hQ : Ac.Hit (Xv.ground) B _ Q.relative _:= revenueX YH Xq P₀ Tq (hR.symm ▸ hf') HI HH ht' hi' hw' hB.1 hB.2.2 he'.1
   have hl : Ac.Hit XU.ground B (fun i=>Real.exp 1* Port.shells V N B Z (coreRate L.L x) i) Q.relative (betaF su x L.L ^(-(3/8):ℝ)):= hZ _ (fun i=> swaddled YH V i)
   refine ⟨Zg,r,d+1,b1,N₁,hr,hA.2.1,⟨knit L H K P₀ YH G V Xg F hxg hf hb hv' hg hQ hl hg' hx (applications YH P₀ Xq hB.1 (hR.symm ▸ hf') HI HH he.1 hQ he'.1 ht) (grassE P₀ HI H₂ (Real.one_le_exp (mul_nonneg zero_le_one (fan_pos ..).le)) (Real.one_le_rpow hkS hv.le)) ht,?_⟩,?_⟩
   · intro V₀ C₁ b₁ e q₀ r₀ A Θ B' n k Ξ hK hV₀
     let Xx:=sailP YH Xg N; have hJ: β=Y'.beta:=rfl
     have hI:=iceM YH V hT hz Wq A (v' x) χ (fun FS Z hv hq hx i hh hm w hJ=> by
         have hQ := cargoW (L:=L) (O:=K) (d:=H) Z w o.a o.large (show 0< Z.t from (hv.symm ▸ hJC.room).fiery) _ hJ
         exact hi₁ c f L H rfl O Ds m' hM hh0 W₀ V S₁ TD FS Z rfl hJC.room hT hv hx hkF i hh w _ (marks i S₁.ratio B) hQ hm)
     obtain ⟨hΦ,hM'⟩:= hvG c f S₁ TD Y' (wood G₂ 0 L.land) _ _ rfl hxg _ YH χ A hkF hV₀
     have hN:=hj f c L H G₂ fQ W₀ _ _ V XU.ground rfl hz.growth hz.toll (hq c f _ rfl) (fun i=>swaddled YH V i) hl
     have h:=liquid (Λ:=v' x) YH Xq P₀ Tq A (heightP L.L x) Z χ Wq (hR.symm ▸ hf') HI HH hB.1 (fan_pos ..).le
     have hf := King.fuse Xv (united XU Xx) (King.induced Xv Ξ hK hP h) (King.fuse XU Xx (King.induced XU Ξ hK (bridgeC YH V hT hz.growth) hI) (King.induced Xx Ξ hK (sailors YH hxg hr) hΦ))
     have hs:= King.applause (united Xv (united XU Xx)) hf
     rw [add_zero q₀, (show 0+(_+1)=romp L.L from ?_),max_self, max_eq_right (show 0 ≤18*B from Nat.zero_le _)] at hs
     swap; · rw [Nat.zero_add]; rfl
     refine ⟨_,hs,?_⟩
     have hx := heights_factor (betaF su x L.L ^(3/5:ℝ)) _ _ _ hQ (fun _=> rfl) (show 0 ≤ _ from by positivity)
     have ho i:= Labels.together Xv.ground _ _ hx (Labels.together XU.ground _ _ hN hM') i
     intro j; convert! ho j using 1; ext i; rcases i with i|i|i <;> first|rfl|skip
     · by_cases h:waxV i=none <;> simp [glazeL,tailTax,h]<;>rfl -- beware
     by_cases h:i.2=none<;>simp [glazeL,tailTax,h]<;>rfl
   intro I' htI gQ R'P G'V HZ' hjG QG'
   let M' := MassiveQCD.Ribbon.ample N I'
   let Xx := sailP YH Xg N
   let xs := closet YH Xq Tq R'P G'V Z
   let Xu' := loommark I' XU; let Xx' := loommark I' Xx; let xg := vantage L H K YH G V Xg R'P G'V Z
   have hQ' : R'P.Coins dV dX (fan L.L θ x) R.threshold:=hR.symm ▸ hjG
   have hpU:XU.Famous:=bridgeC YH V hT hz.growth; have hpX:Xx.Famous:=sailors YH hxg hr
   have hΨ:= ensembleX YH Xq Tq R'P G'V Z HZ' he.1 rfl (MassiveQCD.Stitch.Tablet.tonal G N B) hP ht hQ' (hR.symm ▸ hf') hB.1
   have hΨ':xg.Famous:= jungle xs (united Xu' Xx') hΨ (jungle Xu' Xx' (loping I' XU hpU) (loping I' Xx hpX)); have hXg : xg.gator := entwine xs (united Xu' Xx') (residentG YH Xq Tq R'P G'V Z HZ' he.1) (entwine Xu' Xx' (lofty I' XU (Fleet.branch YH V hz.growth hT)) (lofty I' Xx (sailed YH hxg hr)))
   obtain ⟨Y₀,he₀⟩:= Grove.shaper L H K YH G V Xg R'P G'V Z F θ HZ' hQ' (hR.symm ▸ hf') hB.1 hΨ' hv' hg hn hQ hl hg' ht hx
   refine ⟨ht,R'P.affordable hQ' H₂ (Real.one_le_exp (mul_nonneg zero_le_one (fan_pos ..).le)) (Real.one_le_rpow hkS hv.le),hXg, hΨ',he₀,Y₀,?_⟩
   intro C₁ b₁ e q₀ r₀ A Θ B' n k Ξ hK hV₀
   have hJ: β=Y'.beta:=rfl
   have hI:=iceM YH V hT hz Wq A (v' x) χ (fun FS Z hv hq hx i hh hm w hJ=> by
       have hQ := cargoW (L:=L) (O:=K) (d:=H) Z w o.a o.large (show 0< Z.t from (hv.symm ▸ hJC.room).fiery) _ hJ
       exact hi₁ c f L H rfl O Ds m' hM hh0 W₀ V S₁ TD FS Z rfl hJC.room hT hv hx hkF i hh w _ (marks i S₁.ratio B) hQ hm)
   obtain ⟨hΦ,hM'⟩:= hvG c f S₁ TD Y' (wood G₂ 0 L.land) _ _ rfl hxg _ YH χ A hkF hV₀
   have hN:=hj f c L H G₂ fQ W₀ _ _ V XU.ground rfl hz.growth hz.toll (hq c f _ rfl) (fun i=>swaddled YH V i) hl
   have h:=occupation YH Xq Tq R'P G'V Z HZ' hQ' (hR.symm ▸ hf') hB.1 A (heightP L.L x) (fan_pos ..).le (v' x) χ Wq
   have hf := King.fuse xs (united Xu' Xx') (King.induced xs Ξ hK hΨ h) (King.fuse Xu' Xx' (King.induced Xu' Ξ hK (loping I' XU hpU) (MassiveQCD.Apron.high I' XU hI)) (King.induced Xx' Ξ hK (loping I' Xx hpX) (MassiveQCD.Apron.high I' Xx hΦ)))
   have hs:= King.applause (united xs (united Xu' Xx')) hf
   rw [add_zero q₀, (show 0+(_+1)=romp L.L from ?_),max_self, max_eq_right (show 0 ≤18*B from Nat.zero_le _)] at hs
   swap; · rw [Nat.zero_add]; rfl
   refine ⟨_,hs,?_⟩
   have hx := heights_factor (betaF su x L.L ^(3/5:ℝ)) _ _ _ hQ (fun _=> rfl) (show 0 ≤ _ from by positivity)
   have ho i:= Labels.together Xv.ground _ _ hx (Labels.together XU.ground _ _ hN hM') i
   intro j; convert! ho j using 1; ext i; rcases i with i|i|i <;> first|rfl|skip
   · by_cases h:waxV i=none <;> simp [glazeL,tailTax,h]<;>rfl -- beware
   by_cases h:i.2=none<;>simp [glazeL,tailTax,h]<;>rfl
end YM.QCD.Loom

#print axioms YM.QCD.Loom.summer_ext
