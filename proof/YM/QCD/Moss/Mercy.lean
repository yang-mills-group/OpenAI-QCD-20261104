import YM.QCD.Moss.Spring
/-! # Transparent local filament. Prototype word for an exact period comparison. Forest, corrected slide choices and seam socks. No-limit letters. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Moss
open ConnectedActivityE6
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory ProbabilityTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Coat Animals
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets Horticulture
open Mixed Reserves Trees Beam Beam.Pipe Cove Leaf Lat Loom Loom.Fleet
open PhysicalNext.Repeat PhysicalNext.Repeat.Greenbelt PhysicalNext.Repeat.Deck
open Further.PhysicalPeriodLimitF933 Macrame Stellar Mint
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical PhysicalNext.Repeat.Greenbelt
variable {c f C F L:Side} {P : Teller su}{O:Patch}{D :ℕ}{M:KernelChoices}
variable {h:f.val=c.val*O.L.val}{H:F.val=C.val*O.L.val}{hC:C.val=c.val*D}{he:2≤c.val}
local notation "Lx"=> Lace.project (h:=h) (H:=H) hC he
variable {W κ κ' μ β τ:ℝ} {R:Rep su f}{R':Rep su F}{X:ConnectedActivityE6.Target su P}{o:ConnectedActivityE6.Target.Order su W}
local notation "S"=>stepped M h
local notation "Y"=>stepped M H
variable {T:Tube su (stepped M h)} {T':Tube su (stepped M H)} {N:ℕ}{I J:Type}
variable {K:Cash W τ μ L X o κ T R}{K':Cash W τ μ L X o κ' T' R'}
variable (u:Fleet K I N) (v:Fleet K' J N)(z:EvenA C N →ₐ[ℝ] EvenA c N)
local notation "B"=>radiusB τ
variable {w:Pipe.Clump (stepped M H) J}{r:Pipe.Clump (stepped M h) I}{x:Site C}{n:ℕ}
variable (V:Page hC he u v z w r x n) {E:Tree.Forest (stepped M h).ratio}{G:Tree.Forest (stepped M H).ratio}
variable (hu:u.Famous)(hv:v.Famous) (hN: 2*(2*n+3)<c.val)
variable {A:Coat T E}{A':Coat T' G}
section rose
variable {A B₀ η η' E E': Type*}[MeasurableSpace A][MeasurableSpace B₀][MeasurableSpace η][MeasurableSpace η'][MeasurableSpace E']
variable {D Z':Type*}[NormedAddCommGroup D][NormedSpace ℝ D][NormedAddCommGroup Z'][NormedSpace ℝ Z'][CompleteSpace Z'][CompleteSpace D]
variable [MeasurableSpace D][BorelSpace D][SecondCountableTopology D][MeasurableSpace Z'][BorelSpace Z'][SecondCountableTopology Z'] -- missing norm omit E
variable (m:Measure A) (m':Measure B₀)(n:Measure η)(p:Measure η') (q:Measure E')
   (x:B₀→E')(y:A→ E')(hy:MeasurePreserving y m q) (hx:MeasurePreserving x m' q) (b:A→ B₀)(g:E'→ B₀)(hg:Measurable g)(hb:∀ i, x (b i)=y i)(hp:∀ i, x (g (x i))=x i)
include hy hx hg hb hp in
lemma ledgers (D' :B₀→Z') (F:A→Z') (he:Measurable D') (hf: ∀ i j,x i=x j→ D' i=D' j)(hu:∀ i,F i=D' (b i)):
   (∫ i,D' i ∂m')=(∫ i,F i ∂m):=by
    let G':=D' ∘ g; have hh : Measurable G':=he.comp hg
    have heq i:F i=G' (y i):= by rw [← hb i]; exact (hu _).trans (hf _ _ (hp _).symm)
    have ht : D'=G' ∘ x:=funext fun i=>hf i _ (hp i).symm
    nth_rw 1 [ht]; simp_rw [heq, comp_apply]; rw [← MeasureTheory.integral_map hy.measurable.aemeasurable (hh.aestronglyMeasurable (μ:= m.map y)),← MeasureTheory.integral_map hx.measurable.aemeasurable (hh.aestronglyMeasurable (μ:=m'.map x)),hx.map_eq,hy.map_eq]
variable [SigmaFinite m][SigmaFinite m'][IsProbabilityMeasure n][IsProbabilityMeasure p]
lemma income (j:η)(k:η') (u:η'×B₀→D)(v:η× A→Z')(d:D→L[ℝ]Z') (hu: Integrable u (p.prod m'))(hv: Integrable v (n.prod m))(hp:∀ i j, (∫ k,d (u (j,k)) ∂m')=(∫ k,v (i,k) ∂m)):
    d (∫ i,u i ∂p.prod m')=∫ i,v i ∂n.prod m:=by
      rw [← d.integral_comp_comm hu,integral_prod _ (d.integrable_comp hu),integral_prod _ hv]; let V:= (∫ i,v (j,i) ∂m)
      have hA i:(∫ y,d (u (i,y)) ∂m')=V:=hp j i; have hB i:(∫ y,v (i,y) ∂m)=V:=(hp i k).symm.trans (hA _); simp_rw [hA,hB]; simp
end rose
include hu hv V hN
-- deterministic Well-known seatP equality by y indexes
variable (p q:Finset ℕ)(Hp:Stellar hC he P τ A A')(hw:A.width=o.K)(hk:A.manifest)(hm:A'.manifest)
include Hp hw hk hm
lemma sailor : let t:=podium (Y) su (v.fullA w) (radiusB τ); let m:=arch t A'.relating;
             MeasurePreserving (swim t) A'.dice m ∧ MeasurePreserving (fun x=> swim t (blow (Lx) x)) A.dice m:=by
       intro I a; let C₀:=circuit I A'.relating
       have ht:A'.width=o.K:=Hp.wit.symm.trans hw; have hI:MeasurePreserving (swim I) A'.dice a:= Pond.orbit (K'.laws.data.localP G A' Hp.reached ht hm).sails.fullC.posSemidef _
       have hh i (hg:i∈I):separation x (along (Y) i) ≤ n:= (neighbors_mem ..).1 (V.reaches ((mem_filter.mp hg).2 (along (Y) i) (by rw [separation_self]; omega)))
       have hj:= tempnest (G:=su) (H:=H) (h:=h) (Q:=M) hC he; let y:= Stellar.seed (G:=su) (Lx)
       let e:↥I ↪ Tubular f su:=⟨fun i=> y i.val,fun i j h=> Subtype.ext (hj.point (k:=n) (by omega) x _ _ (hh _ i.2) (hh _ j.2) h)⟩
       have hE:C₀=A.relating.submatrix e e:=by
         ext i j; apply Hp.allocates (D':=2*n) (by omega); refine (separation_triangle _ x _).trans ?_ ; rw [separation_comm _ x]; have hx:=hh _ i.2; have hy:=hh _ j.2; dsimp only; omega
       have Hl:MeasurePreserving (Stellar.mount e) A.dice a:=by change MeasurePreserving _ _ (Poll.sweep C₀);  rw [hE]; exact Stellar.loss e _ (K.laws.data.localP E A Hp.equal hw hk).sails.fullC.posSemidef
       exact ⟨hI,Hl⟩

lemma mease (i:G.Slice su) : Measurable (fun k=>z ((v.suitcase G).capacityP w p (A'.wrapY i) k)):=by
       have hg:= (v.suitcase G).ripeP p w (v.forwarded G hv) A' Hp.reached (Hp.wit.symm.trans hw) hm
       let g (i:G.Slice su × Air F su):EvenA C N:=(v.suitcase G).capacityP w p (A'.wrapY i.1) i.2
       let t:Air F su→G.Slice su × Air F su:=fun k=>(i,k)
       have hh:Measurable t:= measurable_const.prodMk measurable_id
       have hq: Measurable g:=hg.meas; let d:=LinearMap.toContinuousLinearMap z.toLinearMap
       change Measurable (d ∘ (g ∘ t)); exact d.continuous.measurable.comp (hq.comp hh)
lemma samen (i:G.Slice su) (a b:Air F su)(he: swim (podium (Y) su (v.fullA w) (radiusB τ)) a=swim (podium (Y) su (v.fullA w) (radiusB τ)) b): z ((v.suitcase G).capacityP w p (A'.wrapY i) a)=z ((v.suitcase G).capacityP w p (A'.wrapY i) b):=by
         have h2: (v.suitcase G).capacityP w p (A'.wrapY i) a=(v.suitcase G).capacityP w p (A'.wrapY i) b:= (v.suitcase G).lullP p w (v.forwarded G hv) _ _ a b Hp.reached (Village.refl _ _) (by change swim (podium (Y) su _ (radiusB A'.x)) _=swim (podium (Y) su _ (radiusB A'.x)) b; rw [Hp.reached]; exact he)
         exact congr_arg z h2
lemma tabulates (i:G.Slice su)(j:E.Slice su): let W i':= z ((v.suitcase G).capacityP w p (A'.wrapY i) i'); let u₀ j':=(u.suitcase E).capacityP r q (A.wrapY j) j'
              (∫ z,W z ∂A'.dice)=∫ z,u₀ z ∂A.dice:= by
       intro W u₀; let I:=podium (Y) su (v.fullA w) (radiusB τ); let C₀:= circuit I A'.relating; let a:= Poll.sweep C₀
       have ht:A'.width=o.K:=Hp.wit.symm.trans hw
       obtain ⟨hI,Hl⟩:=sailor u v z V hu hv hN Hp hw hk hm
       exact ledgers _ _ _ (swim I) _ Hl hI (Stellar.blow (Lx)) (spill I) (spill_m I) (fun _=>rfl) (fun _=>Pond.settled I _) W u₀ (mease u v z V hu hv hN p Hp hw hk hm i) (samen u v z V hu hv hN p Hp hw hk hm i) (fun t=> (height u v z V hv hN t (Hp.draws j i) p q).symm)

omit Hp hw hk hm
set_option maxHeartbeats 350000 in
lemma gravity (p q:Finset ℕ)(Hp:Stellar hC he P τ A A')(hw:A.width=o.K)(hk:A.manifest)(hm:A'.manifest):
    z (call A' ((v.suitcase G).capacityP w p))=call A ((u.suitcase E).capacityP r q):=by
     let g (i:G.Slice su × Air F su):EvenA C N := (v.suitcase G).capacityP w p (A'.wrapY i.1) i.2; let f₀ (i:E.Slice su × Air f su):=(u.suitcase E).capacityP r q (A.wrapY i.1) i.2
     have hA:Integrable g ((G.order su).prod A'.dice):=envPlot ((v.suitcase G).ripeP p w (v.forwarded G hv) A' Hp.reached (Hp.wit.symm.trans hw) hm) _
     have hB:Integrable f₀ ((E.order su).prod A.dice):=envPlot ((u.suitcase E).ripeP q r (u.forwarded E hu) A Hp.equal hw hk) _
     exact income _ _ _ _ A.Y A'.Y g f₀ (LinearMap.toContinuousLinearMap z.toLinearMap) hA hB (fun i j=>tabulates u v z V hu hv hN p q Hp hw hk hm j i)
end YM.QCD.Moss
