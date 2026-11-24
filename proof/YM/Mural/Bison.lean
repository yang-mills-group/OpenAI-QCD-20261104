import YM.Mural.Weld
/-! # Multiplying the polynomial gears by bounded surface tints. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Comet
open QCD QCD.Grass QCD.Finch QCD.Lat Lattice Wilson RG
open Function Finset MeasureTheory Filter Fork Laurent Flume Kit Pine
open scoped ContDiff BigOperators Matrix Matrix.Norms.L2Operator Classical Kronecker
open MassiveQCD MassiveQCD.Apron.Grove Plette Lat
open PaletteT Ribbon
variable {c f:Side}{j k m:ℕ}
variable {V:Type*} [NormedCommRing V] [NormedAlgebra ℂ V] -- unresolved c.L.
-- Mat action followed by rotations. arrays on SOME; reserve unit.
noncomputable def doll (A B:Mat)(i j: Rank):ℂ:= A i.1 j.1*star B j.2 i.2
noncomputable def tot (A B:Mat)(p:Rank→V)(i:Rank):V:=∑ j:Rank,doll A B i j • p j
lemma tots (A B A' B':Mat)(p:Rank→ V)(i:Rank): tot A B (tot A' B' p) i=tot (A*A') (B*B') p i:=by
   unfold tot; simp_rw [Finset.smul_sum, smul_smul]; rw [sum_comm]; apply sum_congr rfl; intro j _; rw [← Finset.sum_smul]; apply congr_arg (· • p j); unfold doll; rw [Fintype.sum_prod_type]; simp only [star_mul,Matrix.mul_apply,Finset.sum_mul, Finset.mul_sum]; rw [Finset.sum_comm]; apply sum_congr rfl; intro a _; apply sum_congr rfl; intro i _; ring
lemma taxes (A B:Mat)(p:Rank→V)(r:ℂ)(i:Rank): tot A B (fun i=>r • p i) i=r • tot A B p i:=by unfold tot; rw [Finset.smul_sum]; exact sum_congr rfl fun i _=>smul_comm ..
lemma launch (u v:Site f)(g:Lat.Frame f)(x:Option Rank→V)(hx:x none=0)(i:Rank): aggregate (fun j=> fieldD u v g (some i) j) x= tot (colour (g u)) (colour (g v)) (fun i=> x (some i)) i:=by
   unfold aggregate; rw [Fintype.sum_option,hx,smul_zero,zero_add]; apply sum_congr rfl; intro j _; unfold fieldD breadth doll -- tot likely already expanded from apply
   simp [mul_comm]
noncomputable def muster (A B:Mat)(z:ℂ)(p:Option Rank→V) (i:Option Rank):V:=match i with
    | some i=> z • tot A B (fun j=> p (some j)) i
    | none=> 0
variable (A B A' B':Mat)(X Y P Q:Site f)(x y:Site c) (g:Lat.Frame f)(h:Lat.Frame c)
variable (ha:A'=colour (h x)* A*star (colour (g P)))(hb:B'=colour (h y)* B*star (colour (g Q)))
include ha hb
lemma medals (z:ℂ)(T: V→ₐ[ℂ]V)(p q:Option Rank→ V)(hp:q none=0) (hx:Binds (fieldD P Q g) T p q): Binds (fieldD x y h) T (muster A' B' z p) (muster A B z q):=by
     let x1:= colour (g P); let x2:=colour (g Q); let y1:=colour (h x); let y2:=colour (h y); let p0 i:= q (some i)
     have h1:A'*x1=y1*A:=by rw [ha,Matrix.mul_assoc,show star (colour (g P)) * x1=(1:Mat) from su.mat_star_mul _,mul_one]
     have h2:B'*x2=y2*B:=by rw[hb, Matrix.mul_assoc,show star (colour (g Q))*x2=(1:Mat) from su.mat_star_mul _,mul_one]
     intro i; cases i with
     | none=> simp [fieldD,muster,aggregate,map_zero]
     | some i=>
            rw [launch x y h (muster A B z q) rfl]; change T (z • tot A' B' (fun i=>p (some i)) i)=tot y1 y2 (fun i=> z • tot A B p0 i) i; rw [taxes,map_smul]; apply congr_arg; have hh:∀ i:Rank,T (p (some i))= tot x1 x2 p0 i:=fun i=>(hx (some i)).trans (launch P Q g q hp i)
            rw [show T (tot A' B' (fun j=> p (some j)) i)= tot A' B' (tot x1 x2 p0) i from (?_),tots, tots, h1,h2]; unfold tot; rw [map_sum]; apply sum_congr rfl; intro j _; rw [map_smul,hh]; rfl
omit ha hb
open QCD.Mural MassiveQCD.Stitch MassiveQCD.Apron.Grove.PrintR Plate Cupola Twist
variable {I E:Type}{N:ℕ} (Z:PrintR f N Rank I E) (D₁ D₂: Grid f→ Mat)(z:ℂ)(S:Support f)
-- same supports. Reanchoring independent of addr ordered observations.Foot and Hat.
noncomputable def trestle : PrintR f N Rank I E:=⟨Z.srcE,Z.srcK,fun i j v=>muster (D₁ v) (D₂ v) z (fun k=>Z.etaE k j v) i,fun i j v=> muster (D₁ v) (D₂ v) z (fun k=> Z.etaK k j v) i⟩
local notation "Ψ"=> Tine f N Unit
local notation "Tz"=> trestle Z D₁ D₂ z
local notation "Z★" i=>PrintR.regE Tz i
local notation "Y★" i=> PrintR.regK Tz i
lemma vellum (i:Option Rank)(j:I)(U:Grid f)(v:ℝ): Reel.mist (Z★ i) v j U=muster (D₁ U) (D₂ U) z (fun k=> Reel.mist (Z.regE k) v j U) i:=by
    unfold Reel.mist; let S:= (Z.srcE.addr j).support; by_cases hx: Healthy v S U; swap; · rw [masked_ne _ _ _ _ (show ¬ Healthy v ((Z★ i).addr j).support U from hx)]; simp_rw [show ∀ k: Option Rank, masked v ((Z.regE k).addr j).support ((Z.regE k).mark j) U=0 from fun k=>masked_ne v _ _ U hx]; cases i<;> simp [muster,tot]
    rw [masked_eq _ _ _ _ (show Healthy v ((Z★ i).addr j).support U from hx)]; simp_rw [show ∀ k:Option Rank, masked v ((Z.regE k).addr j).support ((Z.regE k).mark j) U=(Z.regE k).mark j U from fun k=>masked_eq v _ _ U hx]; rfl
variable (O:BudgetPoint)(Sg:Support f)(Zp Xp:Unit→Site f)(hP: Z.Fides Zp S O (fieldD P Q))
variable (v0 v1:Lat.Frame f→Site f)(Gv:Lat.Frame f→ Lat.Frame c)
variable (hD:∀ k i, D₁ (gauge k i)=colour (Gv k x)*D₁ i*star (colour (k P))) (hE:∀ k i,D₂ (gauge k i)=colour (Gv k y)*D₂ i*star (colour (k Q)))
lemma living (T:Finset Unit)(p p': Unit→ Site f)(g:Option Rank→ Ψ)(S:Support f)(hh:∀ i:Rank,Stitch.lights T S p qT (g (.some i))) (i:Option Rank) (u v:Mat)(z:ℂ) : lights T S p' qT (muster u v z g i):=by
     unfold muster
     cases i with | none=> exact ⟨polite_nil ..,clad.nil _⟩ | some i=>
       have hz: Polite qT T (tot u v (fun j=>g (some j)) i):=by
           unfold tot Polite; rw [map_sum]; exact Submodule.sum_mem _ fun j _=> ((hh j).1.smooch (doll u v i j))
       refine ⟨hz.smooch z, fun j=>?_⟩
       change pluck (Cove.Keys f N) j (z • tot u v (fun j=> g (.some j)) i) ∈ _; unfold tot; rw [map_smul,map_sum]; apply Subalgebra.smul_mem; apply Subalgebra.sum_mem; intro i _; rw [map_smul]; exact Subalgebra.smul_mem _ ((hh i).2 j) _
lemma warpMeas (hp:Continuous D₁)(hv:Continuous D₂) (i:Option Rank)(g:Option Rank→ Grid f→ Ψ)(h:∀ i, Measurable (g (.some i))): Measurable (fun V=>muster (D₁ V) (D₂ V) z (fun i=>g i V) i):=by
     cases i with
     | none=> exact measurable_const
     | some i=>
       unfold muster tot; dsimp only
       suffices hx:Measurable (fun V=>∑ j:Rank, doll (D₁ V) (D₂ V) i j • g (some j) V) from by exact hx.const_smul z
       refine Finset.measurable_sum _ fun j _=>?_ 
       refine Measurable.smul (f:=fun x=>doll (D₁ x) (D₂ x) i j) ?_ (h j)
       suffices h:Continuous (fun x=>doll (D₁ x) (D₂ x) i j) from h.measurable
       unfold doll; fun_prop
variable (hc: Continuous D₁)(hd:Continuous D₂)(hB0:LocalOn S D₁)(hB1:LocalOn S D₂)(hs: Sg⊆ S)(hy: Xp () ∈ Sg)
include hP hD hE hc hd hB0 hB1 hs hy
set_option maxHeartbeats 540000 in
lemma bandT (k:Lat.Frame f) : JointE Xp qT (Tz).srcE Sg O.threshold k (fieldD x y (Gv k)) (Tz).etaE:=by
      let h₁:=hP.tinted k
      refine ⟨fun i=> ?_,fun i V=>?_,fun j V=>?_⟩
      · let P:= Z★ i; have hi:=h₁.blocking i
        refine ⟨hi.stays,fun j=>?_ , fun j=>warpMeas D₁ D₂ z hc hd i (fun k=> (Z.regE k).mark j) (fun i=> (h₁.blocking (.some i)).permit j), fun j U V h=>?_,fun j v=>living (P.z j) Zp Xp (fun k=>(Z.regE k).mark j v) (P.addr j).support (fun i=> (h₁.blocking (.some i)).stage j v) i (D₁ v) (D₂ v) z,fun j=> hs.trans (hi.boast j)⟩
        · intro x hx; obtain ⟨i,hi',rfl⟩:=mem_image.mp hx; cases i; exact hi.boast j (hs hy)
        change muster (D₁ U) _ z (fun k=>(Z.regE k).mark j U) i= muster (D₁ V) _ _ (fun k=> (Z.regE k).mark j V) _; have hV:= agrees_mono h (hi.boast j); rw [hB0 U V hV,hB1 U V hV]; cases i with | none=>exact rfl | some i=>
          apply congr_arg (fun x:Ψ=>z • x); apply sum_congr rfl; intro k _; exact congr_arg _ ((h₁.blocking (.some k)).room j U V h)
      · rw [vellum]; rfl
      simp_rw [show ∀ i:Option Rank,∀ U, Reel.mist (Z★ i) O.threshold j U=muster (D₁ U) (D₂ U) z (fun k=> Reel.mist (Z.regE k) O.threshold j U) i from fun _ _ =>vellum ..]
      exact medals _ _ _ _ P Q x y k (Gv k) (hD k V) (hE k V) z _ _ _ (h₁.neutral j V) (h₁.sense j V)
set_option maxHeartbeats 420000 in
lemma bandS (k:Lat.Frame f) : JointK Xp qT (Tz).srcK (Tz).etaK Sg O.threshold k (fieldD x y (Gv k)) :=by
    let h₂:= hP.rise k; refine ⟨fun i=>?_,fun _ _=>rfl, fun j V=>?_⟩; swap; · let xV v i:=Z.etaK i j v; exact medals (D₁ V) (D₂ V) _ _ P Q x y k (Gv k) (hD k V) (hE k V) z (Tablet.dance Unit k N) (xV (gauge k V)) (xV V) (h₂.unit j V) (h₂.sense j V)
    let P:= Y★ i; have hi:=h₂.blocking i
    refine ⟨hi.commits,fun j=>?_,fun j=>warpMeas D₁ D₂ z hc hd i (fun k=>(Z.regK k).mark j) (fun i=>(h₂.blocking (.some i)).matters j), fun j U V h H=>?_, ?_,fun j v=>living (P.z j) Zp Xp (fun k=>(Z.regK k).mark j v) (P.addr j).place (fun i=>(h₂.blocking (.some i)).budget j v) i (D₁ v) (D₂ v) z,fun j=> hs.trans (hi.rails j)⟩
    · intro x hx; obtain ⟨u,hu,rfl⟩:=mem_image.mp hx; cases u; exact hi.rails j (hs hy)
    · change muster _ _ z (fun k=>(Z.regK k).mark j U) i= muster _ _ _ (fun k=> (Z.regK k).mark j V) _; have hV:= agrees_mono h (hi.rails j); rw [hB0 U V hV,hB1 U V hV]; cases i with| none=>rfl| some i=>
        apply congr_arg (fun x:Ψ=>z • x); apply sum_congr rfl; intro k _; exact congr_arg _ ((h₂.blocking (.some k)).reads j U V h H)
    intro j U h; by_contra he; apply h; change muster _ _ _ (fun k=>Z.etaK k j U) i=_; have hz i:Z.etaK (.some i) j U=0:=not_not.mp fun h=>(he ((h₂.blocking (.some i)).mask j U h)) -- ¬¬ Eq?
    cases i with | none=>exact rfl|some i=>simp [muster,tot,hz]
lemma textT : PrintR.Fides Tz Xp Sg O (fun k=>fieldD x y (Gv k)):=⟨bandT P Q x y Z D₁ D₂ z S O Sg Zp Xp hP Gv hD hE hc hd hB0 hB1 hs hy,bandS P Q x y Z D₁ D₂ z S O Sg Zp Xp hP Gv hD hE hc hd hB0 hB1 hs hy⟩

end YM.QCD.Comet
#print axioms YM.QCD.Comet.medals
#print axioms YM.QCD.Comet.textT
