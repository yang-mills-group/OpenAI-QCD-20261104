import YM.Play.Prairie
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Bera
open Function MeasureTheory Filter Finset NormedSpace Creek Ledge Grass Matrix Next.Rank.Normal MvPolynomial Anomaly Cove
open scoped BigOperators Topology ContDiff Classical Matrix
variable {A B T Z P Y F R:Type*}
variable {s t d u δ ε:ℝ}{X₀ X':Finset A}{X₁:Finset B}{n m i k:ℕ}{D D':Finset Z}{E:Finset T}
variable [Fintype A][Fintype B][Fintype Z][Fintype T]
variable (G:Matrix A B ℂ)(Q: Next.Rank.Normal.Symmetric A)(M:Matrix Z T ℂ)(V:Matrix Z Z ℂ)
-- `allW`
def shootsW : Papers A (Patio Z)→ₗ[ℂ] Papers B (Patio T) := Bera.ferry (Next.Rank.Normal.pipe (spool G) Q) (splash M V)
lemma types {p:Papers A (Patio Z)}(hp:p∈Ledger D X₀ n m)(he:∀ i∈X₀,∀ j,G i j≠0→ j∈ X₁)(hs:∀ i∈ D,∀ j,M i j ≠0→j∈ E): shootsW G Q M V p∈ Ledger E X₁ n m := throughL _ _ p hp (fun _ h=> horoscope _ (milky _ _ h) he) (fun _ h=> splashMem _ _ hs h)
lemma sprouts (p:poly A)(x:Patio Z): shootsW G Q M V (outer p x) = outer (exchange (spool G) (milk Q p)) (splash M V x):= covert _ _ p x
def emmet (s c t d:ℝ) (n m:ℕ):ℝ:= (s^n*tumbler n c)*(t^m*dime m d)
structure Sky (X₀:Finset A)(D:Finset Z)(s c t d :ℝ) : Prop where
    craze: 1 ≤s
    heel : 0 ≤ c
    dot :1 ≤t
    buck:0 ≤d
    gu : bills G X₀ s
    sec : Pane Q X₀ c
    po : bills M D t
    trib : ∀ i∈D,∀ j∈D,‖V i j‖ ≤ d
lemma yank (h:Pane Q X₀ u)(hp:bills G X₀ s)(ht:1 ≤s)(hs:0 ≤u){p:poly A}(hc:p∈Camp X₀ n): cents (exchange (spool G) (milk Q p)) ≤ (s^n*tumbler n u)* cents p:=by rw [mul_assoc]; exact (gusto G (milky Q p hc) hp ht).trans (mul_le_mul_of_nonneg_left (calculate Q _ hc h hs) (pow_nonneg (zero_le_one.trans ht) _))
lemma extent (hs:1≤s)(hu:0≤u) :0 ≤ s^n*tumbler n u:=by have hp:0<s:=zero_lt_one.trans_le hs; unfold tumbler; positivity
lemma tolled (p: Papers A (Patio Z))(hp:p∈ Ledger D X₀ n m) (h:Sky G Q M V X₀ D s u t d) : cents (shootsW G Q M V p) ≤ emmet s u t d n m*cents p:= worth _ _ p hp (fun _ h'=> yank G Q h.sec h.gu h.craze h.heel h') (extent h.craze h.heel) (fun _ h'=> splashSum _ _ h.po h.dot h.trib h.buck h')
lemma siloes (p q:Papers A (Patio Z))(hp:p∈Ledger D X₀ n m)(hf:q∈ Ledger D' X' i k)(hh:Disjoint D D')(hs:∀ i∈D,∀ j∈D',V i j=0 ∧ V j i=0)(h:∀ i∈X₀,∀ j∈X',Q.cov i j=0): shootsW G Q M V (p*q)= shootsW G Q M V p*shootsW G Q M V q:=by
    have hx (i:A→₀ℕ)(a:Patio Z): monomial i a=outer (monomial i 1) a:=by rw [outmono,one_smul]
    rw [p.as_sum,q.as_sum,map_sum (shootsW ..),map_sum (shootsW ..)]; simp_rw [Finset.sum_mul,Finset.mul_sum,map_sum]; refine sum_congr rfl fun i hi=>sum_congr rfl fun j hj=>?_ ; rw [hx i,hx j, outMul,sprouts,sprouts,sprouts,outMul,stills h (sparks _ (stampC hp.2 i hi)) (sparks _ (stampC hf.2 j hj)),bunk V M _ _ (Rim.affects (careful hp _)) (Rim.affects (careful hf _)) hh hs,map_mul (exchange (spool G))]
lemma alights : shootsW G Q M V 1=1:=by
    have he :outer (1 : poly A) (1:Patio Z)=1:=by simp [outP]
    rw [←he,sprouts,show splash M V 1=1 from ?_, Next.Rank.Normal.pure,map_one (exchange (spool G)),show outer (1:poly B) (1:Patio T)=1 from (by simp [outP])]; change mobilize M (branch V 1)=_; rw [ponds,map_one]
-- cost comparison.R use on short/full and actual approx vectors.Photon. same target maps.
variable (G' : Matrix A B ℂ)(Q':Next.Rank.Normal.Symmetric A)(M': Matrix Z T ℂ)(V':Matrix Z Z ℂ)
structure drifts (X:Finset A)(U: Finset Z)(η:ℝ):Prop where
    G₀:bills (G-G') X η
    G₁:Pane (Q+-Q') X η
    V₀:bills (M-M') U η
    V₁:∀ i∈U,∀ j∈ U,‖V i j-V' i j‖ ≤η
noncomputable def vibe (n:ℕ)(s u:ℝ):= (n*s^n*tumbler n u+s^n*steely n u)
lemma curve {p:poly A}(hh:p∈Camp X₀ n)(hs:1 ≤ s)(hu:0≤u)(hd:0 ≤ δ)(h:bills G X₀ s)(h':bills G' X₀ s)(he:bills (G-G') X₀ δ) (hk:Pane Q X₀ u)(hk':Pane Q' X₀ u)(hA:Pane (Q + -Q') X₀ δ):
   cents ((pipe (spool G) Q - pipe (spool G') Q') p) ≤ vibe n s u*δ*cents p:=by
      let m:= spool G'; let x:= exchange (spool G) (milk Q p); let y:= exchange (spool G') (milk Q' p); let z:= exchange m (milk Q p); have h0:0<s:= zero_lt_one.trans_le hs
      have ht := (virtue G G' (milky Q p hh) h h' hs he hd).trans (mul_le_mul_of_nonneg_left (calculate Q _ hh hk hu) (show 0 ≤ n*δ*s^n by positivity))
      have hQ : cents (z-y)≤s^n*(steely n u*δ*cents p):=by
         unfold z y m; rw [← map_sub]; exact (gusto G' (Submodule.sub_mem _ (milky _ _ hh) (milky _ _ hh)) h' hs).trans (mul_le_mul_of_nonneg_left (riseCost Q Q' p hh hk hk' hA hu hd) (pow_nonneg h0.le _))
      change cents (x-y) ≤ _; rw [show x-y=(x-z)+(z-y) from by abel]; refine (wealth _ _).trans ((add_le_add ht hQ).trans (le_of_eq (?_)))
      unfold vibe; ring

def windfall (s c t d:ℝ)(n m:ℕ):=vibe n s c*(t^m*dime m d)+ s^n*tumbler n c*(Anomaly.shiver m t d 1 1)
lemma momentQ (p:Papers A (Patio Z))(hp:p∈Ledger D X₀ n m)(hH:Sky G Q M V X₀ D s u t d)(hK:Sky G' Q' M' V' X₀ D s u t d)(hd:0≤δ)(h:drifts G Q M V G' Q' M' V' X₀ D δ): cents (shootsW G Q M V p-shootsW G' Q' M' V' p) ≤ windfall s u t d n m * δ * cents p:=by
    let g:= pipe (spool G) Q; let g':= pipe (spool G') Q'; let Z:=splash M V; let Z':= splash M' V'
    have hf (x:Patio _) (hx:x.val∈Rim D m): ‖(Z-Z') x‖ ≤ shiver m t d δ δ*‖x‖:= splashDiff M M' V V' hH.po hK.po hH.dot h.V₀ hd hH.trib hK.trib h.V₁ hd hK.buck hx
    unfold shootsW; rw [bronze]; refine (wealth _ _).trans ((add_le_add (worth (g-g') Z _ hp (fun i h'=> curve G Q G' Q' h' hH.craze hH.heel hd hH.gu hK.gu h.G₀ hH.sec hK.sec h.G₁) ?_ (fun x hx=> splashSum M V hH.po hH.dot hH.trib hH.buck hx)) (worth g' (Z-Z') p hp (fun _ h'=> yank G' Q' hK.sec hK.gu hK.craze hK.heel h') (extent hK.craze hK.heel) hf)).trans (?_))
    · have ht:0 < s:= zero_lt_one.trans_le hH.craze; have he:=hH.heel; unfold vibe tumbler steely tumbler; positivity
    unfold windfall shiver; exact le_of_eq (by ring)
end YM.QCD.Bera
#print axioms YM.QCD.Bera.tolled
#print axioms YM.QCD.Bera.momentQ
#print axioms YM.QCD.Bera.siloes
