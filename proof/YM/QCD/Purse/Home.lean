import YM.QCD.Shell.Nil
/-! # Fit short-pick upper; furnish all Pack constructors. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Jets.Touch
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Leaf Tee Flume Orbit Quarry Stationary Fork Pine YM.Next.Free Push.AbsoluteSums Footprint Trees
open Sun ConnectedActivityE6 Pressure Animals Garden
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {F j k:ℕ}{L:Side} {x u v a b c ν C D T θ w κ q Y ε e z: ℝ} {i m:ℕ}{f g: ℝ→ℝ}

lemma diamonds (P:Plan j)(F:ℕ)(hj:4≤j)(hk :4 ≤k)(K:ℝ)(hK:0<K):∃ i:ℕ,∀ L:Side,i≤L.val→∀ (w r q a:ℝ),0<w→0<r →∀ b:ℕ,∀ᶠ x in atTop,
    let t:= haloK L x; let δ:=coneK L w x
    ∀ (C f: Side),2*(radiusB x+1)< f.val→∀ (G:Flight j k)(H:f.val=C.val*G.L.val),G.L=L→ ∀ (v X A b' Q m:ℝ)(Z:Offer 1 X A)(U:Offer 2 b' Q), |m|≤t→
       ∀ p:Sun G C f H δ v q r a b (pesto P G H (trunkM Z U t m f)), ∃ η, Fork.Sea G H (radiusB x) δ η q (fiery su x L) p.Z p.V 2 ∧ K*fingers F*η ≤1:=by
  obtain ⟨C,hc,h⟩:=Fork.sizesP (j:=j) P hj hk 2
  obtain ⟨i,hi⟩:= presses P F C K hK hc
  obtain ⟨A,hA,ha⟩:= Fork.travelQ
  refine ⟨i, fun L hl w r q a hW hr b=> ?_⟩
  filter_upwards [filming L hW A, (sol L P C q A a r w hW hr b 2|>.mul_left (K*fingers F)).below (by norm_num) (1/2) (by norm_num), Delay.shift_pos su L] with x hx hp hX
  intro t δ c f hB G H hL v R D b' Q m Z U hm p
  let s:=radiusB x; let B:=tabP P G.L C q A a r v |m| (fiery su x L) δ 2 s b
  have hw : 0<δ:=p.positive
  have he : 0 < fiery su x L:=mul_pos (inv_pos.mpr (Real.sqrt_pos.mpr hX)) (Real.exp_pos _)
  refine ⟨B, horns s 2 b hr he.le hw p.stable p.Z0 p.V0 (h G f c H) hA hx (fun u i he'=> ha _ _ _ u i hB he.le he'),?_⟩ -- x binder likely unknown; fiery G.L? horns estate uses travel with t. 
  have hV : B ≤ tabP P L C q A a r 0 t (fiery su x L) δ 2 s b:=by
      unfold B; rw [hL]; unfold tabP
      have hb:=p.stable.calf; have hv:=healthy P L; have hx:= mass_pos L -- fill
      gcongr
  apply le_trans (mul_le_mul_of_nonneg_left hV (by unfold fingers; positivity)); have ht:= hi L hl
  have hh : K*fingers F * (tabP P L C q A a r 0 t (fiery su x L) δ 2 s b-C*Kit.slope L/(L.val:ℝ)) ≤ 1/2:= (le_abs_self _).trans hp; rw [mul_sub] at hh; linarith
open Lattice RG Ac
-- upgrade Census ANY Campaign. H perhaps F=0. GET η≥0 from leases W[/concat].
variable {s τ A:ℝ}
variable {l:ℕ} {p t T' u' v' y₀ :ℝ}
lemma seaFact {φ f: Side}{D: Flight j k}{H': f.val=φ.val*D.L.val}{G'} (P:Jets.Sun D φ f H' u v q p w l G') {η} (he: Sea D H' i u η q x P.Z P.V 2): 0 ≤ η:=by
    obtain ⟨W,hW,hq,_⟩:= (he 0).1.leases; exact (sum_nonneg (fun i _=> mul_nonneg (meets_nn ..) (hW i))).trans hq
lemma coupons {l r:ℕ}{f c: Side}{H':Flight j k}{V:f.val=c.val*H'.L.val}{T: Grid f→Sheet f}{S v u:ℝ}(Z:Sun H' c f V u v q t S l T) {E J:Type} (p':Rise f F E J)(x y:ℝ) (σ:E→ℝ)(β:J→ℝ)
   (X:Cove.Fj (Tr f) E J→Support c) (hs : Count (Z.equip F r) p' X) (hx:0≤a) (hz: Ready X i (paidSet (Z.equip F r) p' (fun i=>Real.exp 1*terra Z F r x y i) σ β T' u' v' 1) a y₀ ε e) (hy:y₀≤1): ∀ j,terra Z F r x y j≤1:=by
    intro j; by_cases hp:(X (.inl j)).Nonempty
    · obtain ⟨a,hm⟩:=hp; have hv:= budget_sum (hz.2.2.2.2.2 a) {Sum.inl j}; rw [sum_singleton,if_pos hm] at hv
      have he : 0 ≤ Real.exp 1*terra Z F r x y j:= hz.2.2.2.2.1 (Sum.inl j); have ht: Real.exp 1*terra Z F r x y j ≤ 1 := (le_mul_of_one_le_right he (Real.one_le_exp (by have hh:= hz.2.1; positivity))).trans (hv.trans hy)
      nlinarith [Real.add_one_le_exp 1]
    have hQ:roomK j=∅:= by
       apply not_nonempty_iff_eq_empty.mp; intro H; apply hp; refine (H.image ((sliceL H' V).parent)).mono ?_; intro i hi; apply hs.budget (.inl j); apply image_subset_image (halo_subset _ _) hi
    rcases j with j|j
    · exact (terra_zero Z j r F hQ).1.trans_le zero_le_one
    exact (terra_zero Z j r F hQ).2.trans_le zero_le_one
structure Wrist (P:Plan j)(k: ℕ)(F n:ℕ)(L:Side)(u ρ a K θ r q t l C:ℝ)(i:ℕ):Prop where
    pays : ∀ᶠ x in atTop, let b:=radiusB x; let δ:=coneK L r x; let g:=haloK L x
                        ∀ f c : Side, 2*(b+1)< f.val → ∀ (X U A D d:ℝ)(Z:Offer 1 X A)(U':Offer 2 U D)(m₀:ℝ)(J:Flight j k)(H:f.val=c.val*J.L.val), J.L=L→ |m₀|≤g→
                        let T:= pesto P J H (trunkM Z U' g m₀ f)
                        ∀ T':Sun J c f H δ d q ρ l i T, ∃ φ, Sea J H b δ φ q (fiery su x L) T'.Z T'.V 2 ∧ 0 ≤ φ ∧ 32*K*fingers F*φ ≤1∧ ∀ {E V:Type}[Countable E][Countable V],∀ (R:Rise f F E V)(β:E→ℝ)(Q:V→ℝ),
                          let p:=T'.equip F b; let y:=fan L θ x; let h:=K*y; let W:=roof p R n b
                          let μ j:= Real.exp 1*terra T' F b y h j
                          let Y:=paidSet p R μ β Q C (cashM L θ x) (taxK L x (1/2)) 1
                          Cents R β Q y (fiery su x L) → Fill R β Q u u (taxK L x 1) 1 (chip L x) (highR L x) →
                          K*fingers F*q ≤ C ∧ Peak p (fiery su x L) y (K*y) C μ ∧ 1 ≤ cashM L θ x ∧ 1 ≤ taxK L x (1/2) ∧ Ready W b Y a (fan L (-θ-θ/2) x) 1 (fan L (-θ) x) ∧ (∀ j,terra T' F b y h j≤1)
theorem billing (P:Plan j)(F k n:ℕ)(hj:4≤j)(hk:4≤k) (K a u ρ θ:ℝ)(hK:1≤K)(ha:0≤a)(hu:0<u)(hρ:0<ρ)(hθ:0<θ): ∃ m:ℕ,∀ L:Side,m≤L.val→∀ (r q t l:ℝ) (i:ℕ), 0<r → ∃ C:ℝ, 1≤C ∧ Wrist P k F n L u ρ a K θ r q t l C i:=by
   have hw:0<K:=by linarith
   obtain ⟨p,hp⟩:= diamonds P F hj hk (32*K) (mul_pos (by norm_num) hw); obtain ⟨q,hq⟩:=dice P F hj hk K hw
   let z:=ρ/2; let v:= z/4; let d:=u/4
   have hz:0<z:=half_pos hρ; have ht:z<ρ:=half_lt_self hρ; have hv:0<v:=by unfold v; positivity; --indent
   have h1:0<d:=by unfold d; positivity
   have h2:2*d<u:=by unfold d; linarith
   have h3:2*v<z:=by unfold v; linarith
   have ha':0≤a+1:=by linarith
   obtain ⟨g,hg⟩:= Fees.exponent (n+8) h1 ha' h2; obtain ⟨D,hD⟩:=Fees.exponent (n+8) hv ha' h3
   refine ⟨p+q+D+g,fun L hL r Q t l i hr=>?_⟩
   let C:=max 1 (K*fingers F*Q); have hZ:1≤C:=le_max_left ..; have hQ:K*fingers F*Q≤C:=le_max_right ..
   refine ⟨C,hZ,?_⟩; constructor
   filter_upwards [hp L (by omega) r ρ Q l hr hρ i,hq L (by omega) r ρ Q l hr hρ i,lets L θ hθ u 0 a hu K C hw hZ 0 d z Q ρ v v ht F j k (n+8) i ha h2 h1,Seat.keeps (L:=L) (a:=-θ-θ/2)|>.shrinks (by linarith) (D:=1) one_pos, Work.E01.radiusB_tendsto.eventually_ge_atTop 1] with x hM hZ'p hX hQ' hm
   intro b δ t' f c Hf X U A D W Z U' m G H he h T T'; obtain ⟨φ,hV,h⟩:=hM _ _ Hf G H he W X A U D m Z U' h T'
   obtain ⟨η,hΦ,hY⟩:= hZ'p _ _ Hf G H he W X A U D m Z U' (by assumption) T'
   refine ⟨φ,hV, seaFact T' hV,h,?_⟩
   intro E V _ _ R β Q' p y h W μ Y Hm Hκ
   let P₀:= sliceL G H; have hv : P₀.count=L:=he; have hs:= hD _ _ P₀ (hv.symm ▸ (by omega)); have hz:=hg _ _ P₀ (hv.symm ▸ (by omega))
   have hs' : reserve ρ (a+1) (conversion P₀ (n+8)) v:= ⟨hs.1,hs.2.1,hs.2.2.trans ht.le⟩
   obtain ⟨hv,hB⟩:=roofs p R n b le_rfl hm
   obtain ⟨H,H',he,hX⟩:=hX _ _ G T he H _ _ _ T' η hz hs' hs hΦ hY hQ R β Q' W Hm Hκ hv hB
   exact ⟨hQ,H,H',he,hX,coupons T' R y h β Q' W hv ha hX ((le_abs_self _).trans hQ')⟩ -- y,h names
end YM.QCD.Jets.Touch
