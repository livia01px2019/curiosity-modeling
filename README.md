# README
1. **What are you trying to model? Include a brief description that would give someone unfamiliar with the topic a basic understanding of your goal.**

    In this project, we are trying to model music in order to generate models of harmonious and interesting pieces. This includes choosing notes that sound good together, choosing note lengths such that there is a rhythm, and including variation in the music. 

2. **Give an overview of your model design choices, what checks or run statements you wrote, and what we should expect to see from an instance produced by Sterling. How should we look at and interpret an instance created by your spec?**

    In designing the model, we had to make a few design decisions and assumptions. As music is quite subjective and reasonably freeform, we decided to restrict our search space to a subset of the normal 12 pitches in the chromatic scale. We decided to work within a particular scale called the ‘major pentatonic scale’ (containing 5 notes with certain intervals between them). This increases the ease with which decent melodies can be generated.

    Another design choice was regarding variation in note lengths, octaves, and tones in general. Listening to produced melodies and tweaking hyperparameters was a crucial part of development. Eventually, we settled on having only 2 distinct note lengths, 2 main octaves, and a maximum of 2 of the same pitch in a row.

    To guide the development of our model restrictions, our main source of ‘checking’ the predicates was in fact by running the code and listening to the produced melody with an audio visualizer. The subjectivity of music makes it difficult to precisely pinpoint what makes a particular melody ‘good’, which in turn makes high-level testing with examples an incomplete strategy. Instead, listening and modifying predicates was the main source of overall testing of the model. We added simple tests to guarantee that the lower-level predicates correctly differentiated between correct and incorrect models as well. 

    After running an instance, the Sterling visualizer should be opened and <div> should be selected. Executing the included visualizer.js file should both produce a basic overview of the current music score and play the simple melody (turn on your audio!). Note that care should be taken to control the volume and to avoid playing two melodies at the same time (the visualizer will auto-run after pressing the Next button, so don’t additionally press execute).

3. **At a high level, what do each of your sigs and preds represent in the context of the model? Justify the purpose for their existence and how they fit together.**

    The PitchClass sig represents a musical pitch class and we have 12 sigs that extend PitchClass, which represents every possible pitch class (you can think about it as for every C to C section on a piano, there is 1 Pitchclass for every key). 

    The circleOfFifths pred defines the circle of fifths in music, which is a 12-note cycle of pitch classes where 5 consecutive notes on the circle sound harmonious together. 

    The Scale sig represents a set of pitch classes that represent a musical major pentatonic scale that will be in the same key and one pitch class in the set which is distinguished as the header, or first note/tonic note in the scale. The pentScale pred reinforces this, restricting the notes to be 5 notes in the scale that form a consecutive chain in the circleOfFifths and restricting the header to be the tonic pitch class. 

    The Note sig is finally where our actual melody is generated. It defines many characteristics of a note, including the pitch class, octave, and noteLength that it has. We decided to add an accompaniment pitch class and octave for each note as well to add a more interesting aspect to the music. A note sig also has a field called noteLengthRun, which will be used later as an accumulator of noteLengths and to restrict the rhythm. Finally, it has a nextnotes field which points to the next note in the melody. 

    The wellFormed predicate defines some basic characteristics of the Notes, including that it must be a connected chain of notes and that the pitch classes should all be chosen from the scale. 

    The basicSound predicate defines basic characteristics of the Notes so that it sounds harmonious, including making the first and last notes tonic (to give a feeling of “going home” or finality) and controlling the noteLengths and octaves to be within a reasonable range. It also defines the accompaniment to not sound dissonant when combined with the main pitch class. 

    The noteVariation predicate makes the music more interesting by making sure that there are not consecutive repeated notes. 

    The rhythm predicate defines a basic set of rules so that the Notes are divided into measures where each measure has a total noteLength of 4 (if you know music, think a 4/4 time). It also ensures that the last note is on the longer side to give it a feeling of finality. 

    Finally, the soundsNotAwful predicate is a combination of all of the above predicates. 
