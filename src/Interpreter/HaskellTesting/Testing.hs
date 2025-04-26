import ExtractionTests
import Prelude
import Control.Monad.Writer

positive_tests_correct :: [((Process, Action), Maybe Process)] -> Bool
positive_tests_correct [] = True
positive_tests_correct (((p, a), p') : ts) = ((processLocalStepFunc p a) == p') && positive_tests_correct ts

negative_tests_correct :: [((Process, Action), Maybe Process)] -> Bool
negative_tests_correct [] = True
negative_tests_correct (((p, a), p') : ts) = ((processLocalStepFunc p a) /= p') && negative_tests_correct ts

positive_testing :: [((Process, Action), Maybe Process)] -> Writer [String] ()
positive_testing [] = return ()
positive_testing (((p, a), p') : ts) = do
    let b = processLocalStepFunc p a == p'
    case b of
        True -> tell ["\x1b[32mSUCCESS\x1b[0m", show ((p, a), p'),""]
        False -> tell ["\x1b[31mFAIL\x1b[0m", show ((p, a), p'),""]
    positive_testing ts

negative_testing :: [((Process, Action), Maybe Process)] -> Writer [String] ()
negative_testing [] = return ()
negative_testing (((p, a), p') : ts) = do
    let b = processLocalStepFunc p a /= p'
    case b of
        True -> tell ["\x1b[32mSUCCESS\x1b[0m", show ((p, a), p'),""]
        False -> tell ["\x1b[31mFAIL\x1b[0m", show ((p, a), p'),""]
    negative_testing ts

runTests :: IO ()
runTests = do
    let (_, log_pos) = runWriter (positive_testing positive_tests)
    putStrLn "\n\x1b[36m+---------------------+\x1b[0m"
    putStrLn "\x1b[36m|   POSITIVE TESTS    |\x1b[0m"
    putStrLn "\x1b[36m+---------------------+\x1b[0m\n"
    mapM_ putStrLn log_pos
    
    let (_, log_neg) = runWriter (negative_testing negative_tests)
    putStrLn "\n\x1b[36m+---------------------+\x1b[0m"
    putStrLn "\x1b[36m|   NEGATIVE TESTS    |\x1b[0m"
    putStrLn "\x1b[36m+---------------------+\x1b[0m\n"
    mapM_ putStrLn log_neg
