import YM.QCD.Pant.Button
/-! # Turning columns under arbitrary split-phase budgets.
 Usable for body & jet operations on the even subalgebra. K turns still accounted. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Patron
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Leaf Tee Flume Orbit Quarry Stationary Fork Pine YM.Next.Free Push.Local
open Jets Sun Revolve Garden Bay Strut LeafM Sway OrbitG
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c f:Side}{N:ℕ}
variable {G:Grid f→Sheet f}{δ a b c' q t:ℝ}{p:Strut c}{d d':Site c→ℂ}{Z P:Spike}

section scalar
variable {B:Type*}[Fintype B][DecidableEq B]
-- Ring morph pred stable on complex sector (Serenity uses real-axis only).
omit [DecidableEq B] in
lemma swayC (X:Matrix B B ℂ)(v:Patio (Pairs B))(q:ℂ): sways X (q • v)=q • sways X v:=Subtype.ext (map_smul (disguise X) q v.val) -- morph?
lemma regC (v:EvenA c N)(q:ℂ): Regal c N (q • v)= (star q) • Regal c N v:=by
    apply Subtype.ext; change disguise _ (surf _ (q • v.val))=star q • disguise _ (surf _ v.val); rw [map_smulₛₗ,map_smul]; rfl
end scalar
-- Avenir.w
def Chord (X:Matrix (Flavor N) (Flavor N) ℂ):Prop:=X∈unitary _ ∧ ∀ i j,i≠j→ X i j=0
/-- Diagonal vector U(1)^N. No suppressed subgroups in this test. -/
def AccentFit (x:EvenA c N):Prop:=∀ W: Matrix (Flavor N) (Flavor N) ℂ,Chord W → sways (flute _ W) x=x
namespace AccentFit
lemma of_fit {x:EvenA c N}(h:Fit x):AccentFit x:=fun i hi=> h i hi.1
lemma mulC (x:EvenA c N)(h:AccentFit x) (q:ℂ):AccentFit (q • x):=fun i hi=> Eq.trans (swayC _ x q) (congr_arg _ (h i hi))
def RealA (x:EvenA c N):= Regal c N x=x
local notation "V"=>EvenA c N
lemma dated (f:ℝ)(x:EvenA c N)(h:AccentFit x):AccentFit (f • x):=fun g hp=>Eq.trans (Loom.Fleet.eSM _ (OrbitG.phare _) ..) (congr_arg _ (h g hp))
lemma polarizei (v: V)(h:AccentFit v)(X: Sheet c): AccentFit (sways (copies N X) v):=by intro g hh; rw [← choirT,h g hh]
lemma polarizeg (v:V)(h: AccentFit v):AccentFit ((OrbitG.spark _).passL v):=by intro g hh; rw [← novel,h g hh]
lemma facade (v: V)(h: AccentFit v)(x:ℂ)(X:Sheet c)(hx:star x*x=1): sways (copies N (x • X)) v= sways (copies N X) v:=by
    let P:= flute (Lat.Row c) (x • (1:Matrix (Flavor N) (Flavor N) ℂ)); have hh:P=x • 1:=by ext ⟨i,l⟩ ⟨j,b⟩; by_cases h:i=j <;> by_cases hb:l=b <;> simp [P,flute, h,hb,Matrix.smul_apply]
    have hv:sways P v=v:=h _ ⟨unitaryV x _ hx,fun i j hi=>by simp [Matrix.one_apply_ne hi,Matrix.smul_apply]⟩
    rw [show copies N (x • X)=P*copies N X from ?_,← leaps,hv]
    rw [copies_skim, hh,Matrix.smul_mul,one_mul]
lemma coinT (v:V)(h:AccentFit v)(he: Warrant p d Z)(hv:Warrant p d' P): Diode N p Z d v=Diode N p P d' v:=by
    obtain ⟨s,hS,H⟩:= Strut.faith he hv
    apply Eq.trans _ (facade v h s (haze p P d') hS)
    apply congr_arg (fun X=> sways (copies N X) v)
    change rides _ _=s • rides _ _; rw [ride_smul]; exact congr_arg _ (funext H)
lemma gammaT (v:V)(h:AccentFit v)(hp:Warrant p d Z): Regal c N (Diode N p Z d v)=Diode N p Z d (Regal c N v):=by
    let Vw:= (OrbitG.spark _).passL v
    obtain ⟨x,hx,hC⟩:= upright hp
    have hh : haze p Z d*chirality c=x • (chirality c*haze p Z d):=by
       change rides (act p) (lightP p Z d) *rides (Equiv.refl (Site c)) (fun _=>J0)=x • (rides (Equiv.refl (Site c)) (fun _=>J0)* rides (act p) (lightP p Z d)); rw [ride_mul,ride_mul,ride_smul,Equiv.trans_refl,Equiv.refl_trans]; exact congr_arg _ (funext hC)
    change sways (copies N (chirality c)) ((OrbitG.spark _).passL (_))=sways _ (sways (copies N (chirality c)) Vw); unfold Diode; rw [novel,leaps,leaps,← copies_mul,← copies_mul,hh]; exact facade Vw (polarizeg v h) x _ hx -- hx syntax?

end AccentFit
open Loom Loom.Fleet
variable {ι β:Type} (E:Gem c N ι)(J:Patron.Rail c N β)
structure Noted (E:Gem c N ι):Prop where
 gauge i: shadeG (E.view i)
 num i U: AccentFit (E.view i U)
 real i U: Regal _ _ (E.view i U)=E.view i U
structure MixedInk (E:Rail c N ι):Prop where
 gauge i: shadeG (E.warp i)
 num i U: AccentFit (E.warp i U)
 real i U: Regal _ _ (E.warp i U)=E.warp i U
 moves s z k : Warrant s z k→∃ e: Equiv.Perm ι,∀ i,
               ((E.addr (e i)).place=(E.addr i).place.image (act s)) ∧ (E.addr (e i)).inv=(E.addr i).inv.image (act s) ∧∀ U:Grid c, Diode N s k z (E.warp i (sky s U))= E.warp (e i) U -- c N vs binder arity here if `E: Rail c N ι`
structure Keyed (E:Gem c N ι) :Prop where
 notes : Noted E
 turns (s:Strut c)(k:Spike)(d:Site c→ℂ): Warrant s d k→∃ e:Equiv.Perm ι,∀ i,E.addr (e i)=rotateL (E.addr i) s ∧ ∀ V, Diode N s k d (E.view i (sky s V))= E.view (e i) V
lemma noted (h:Noted E): Noted (glean E):=by
   constructor
   · rintro ⟨v,i⟩ U k
     suffices he : sways (Lat.rotates N k) ((glean E).view (v,i) (gauge k U))=(glean E).view (v,i) U by exact congr_arg Subtype.val he
     let P:= spice v (N:=N); change sways _ (averageC c • _) = averageC c • _; rw [eSM _ (phare _),show sky v (gauge k U)=gauge (k ∘ act v) (sky v U) from pull_gauge ..]; apply congr_arg; unfold spice
     rw [custodial k _ (assured v)]; apply congr_arg; exact Subtype.ext (h.gauge i (sky v U) (k ∘ act v))
   · rintro ⟨v,k⟩ U; exact AccentFit.dated _ _ (AccentFit.polarizei _ (h.num k _) _)
   rintro ⟨v,k⟩ U; exact dolled _ (Diode N v _ _ _) ((AccentFit.gammaT _ (h.num k _) (assured v)).trans (congr_arg _ (h.real k _)))

lemma keyed (he:Noted E): Keyed (glean E):=by
   refine ⟨noted _ he,fun v k g hh=>?_⟩
   refine ⟨Equiv.prodCongr (skyEquiv v) (Equiv.refl _),?_⟩; rintro ⟨p,i⟩; refine ⟨?_,fun U=>?_⟩
   · change rotateL (E.addr i) (pod v p)=rotateL (rotateL (E.addr i) p) v; unfold rotateL; congr 1
     · exact Equiv.congr_fun (podA ..) _
     change (E.addr i).support.image _=((E.addr i).support.image _).image _; rw [podA,image_image]; rfl
   change Diode N v k g (averageC c • spice p (E.view i (Strut.sky p (Strut.sky v U))))= averageC c • spice (pod v p) (E.view i (Strut.sky (pod v p) U)); rw [skying,eSM _ (phare _)]; apply congr_arg; change sways _ (sways _ _)=_; rw [leaps,← copies_mul,← beset _ _ _ _ g (ink p)]; exact AccentFit.coinT (E.view i _) (he.num i _) (Strut.comb hh (assured p)) (assured _)

end YM.QCD.Patron
